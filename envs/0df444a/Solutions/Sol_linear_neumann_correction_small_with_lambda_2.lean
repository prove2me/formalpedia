-- Prove2me | solution 2 for linear_neumann_correction_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T08:31:32.64105+00:00
-- url     : https://prove2.me/submissions/9a26cacd-c70e-4b92-a017-abf2617ad04a

import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_linear_neumann_correction_from_diagonal_off_diagonal_bounds
import Theorems.Thm_linear_neumann_diagonal_contribution_small_with_lambda
import Theorems.Thm_linear_neumann_off_diagonal_decoupling_transfer
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_from_coefficient_bound
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
import Theorems.Thm_sign_matrix_coordinate_energy_bounds_from_a1
open MatrixCompletion

open scoped Classical

/-!
Candes–Recht Lemma 4.5 (first Neumann correction), assembled from the
platform's proved pieces.  The diagonal part is `linear_neumann_diagonal_
contribution_small_with_lambda`; the off-diagonal part is obtained from the
decoupling transfer, the decoupled-from-coefficient bound and the scalar
Bernstein / union-bound chain for the coefficient matrix `Q(E)`.  The two
ingredients supplied here are

* `A1(μ₁)` implies `A0(μ₁²)`, so that the coefficient chain can be run with the
  reduced coherence parameter `ν = min μ₀ μ₁²`;
* the absorption of the two-term Bernstein threshold into the Lemma 6.6 scale
  under the `λ` sample-size hypothesis, which works because
  `ν ≤ μ₁ max(√μ₀, μ₁)`.
-/

/-- Monotonicity of the Bernoulli event probability in the event. -/
lemma lnEventMono {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E₁ E₂ : Finset (Fin n1 × Fin n2) → Prop) (h : ∀ Ω, E₁ Ω → E₂ Ω) :
    bernoulliEventProb p E₁ ≤ bernoulliEventProb p E₂ := by
  unfold bernoulliEventProb
  refine Finset.sum_le_sum fun Ω _ => ?_
  have hw : 0 ≤ bernoulliObservationWeight p Ω := by
    unfold bernoulliObservationWeight
    have : 0 ≤ 1 - p := by linarith
    positivity
  by_cases h1 : E₁ Ω
  · rw [if_pos h1, if_pos (h Ω h1)]
  · rw [if_neg h1]
    split_ifs <;> simp [hw]

/-- Assumption `A1(μ₁)` forces both singular coherences to be at most `μ₁²`. -/
lemma lnA0_of_A1 {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) (μ₁ : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hμ₁ : 1 ≤ μ₁) (hA1 : A1 S μ₁) :
    A0 S (μ₁ ^ 2) := by
  obtain ⟨hu, hv⟩ :=
    sign_matrix_coordinate_energy_bounds_from_a1 n₁ n₂ r M μ₁ S hn₁ hn₂ hr hμ₁ hA1
  have : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  have : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  constructor
  · unfold coherence
    have hsup : (⨆ i : Fin n₁, ∑ k, (S.u k i) ^ 2) ≤ μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ) :=
      ciSup_le hu
    calc (n₁ : ℝ) / r * (⨆ i : Fin n₁, ∑ k, (S.u k i) ^ 2)
        ≤ (n₁ : ℝ) / r * (μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ)) :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = μ₁ ^ 2 := by field_simp
  · unfold coherence
    have hsup : (⨆ j : Fin n₂, ∑ k, (S.v k j) ^ 2) ≤ μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ) :=
      ciSup_le hv
    calc (n₂ : ℝ) / r * (⨆ j : Fin n₂, ∑ k, (S.v k j) ^ 2)
        ≤ (n₂ : ℝ) / r * (μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ)) :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = μ₁ ^ 2 := by field_simp

/-- The reduced coherence parameter `min μ₀ μ₁²` is still an `A0` parameter. -/
lemma lnA0_min {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) (μ₀ μ₁ : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hμ₁ : 1 ≤ μ₁)
    (hA0 : A0 S μ₀) (hA1 : A1 S μ₁) : A0 S (min μ₀ (μ₁ ^ 2)) := by
  have h1 := lnA0_of_A1 S μ₁ hn₁ hn₂ hr hμ₁ hA1
  exact ⟨le_min hA0.1 h1.1, le_min hA0.2 h1.2⟩

/-- Abstract form of the two-term absorption: with `A = ν N r L / m` and
`β A ≤ 1`, the Bernstein threshold is dominated by `√(β A)`. -/
lemma lnAbsorbCore (Ctwo Centry Cfro s β A : ℝ) (hCtwo : 0 ≤ Ctwo) (hCentry : 0 ≤ Centry)
    (hCfro : 0 ≤ Cfro) (hs : 0 ≤ s) (hβ : 2 ≤ β) (hA0 : 0 ≤ A) (hA : β * A ≤ 1) :
    Ctwo * (Real.sqrt ((β + 2) * A) * (Cfro * s) + ((β + 2) * A) * (Centry * s)) ≤
      (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * s * Real.sqrt (β * A) := by
  have ht0 : 0 ≤ Real.sqrt (β * A) := Real.sqrt_nonneg _
  have hβA : 0 ≤ β * A := mul_nonneg (by linarith) hA0
  have ht2 : Real.sqrt (β * A) ^ 2 = β * A := Real.sq_sqrt hβA
  have ht1 : Real.sqrt (β * A) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hA
  have hprod : 0 ≤ (β - 2) * A := mul_nonneg (by linarith) hA0
  have h1 : Real.sqrt ((β + 2) * A) ≤ Real.sqrt 2 * Real.sqrt (β * A) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have h2 : (β + 2) * A ≤ 2 * Real.sqrt (β * A) := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  calc Ctwo * (Real.sqrt ((β + 2) * A) * (Cfro * s) + ((β + 2) * A) * (Centry * s))
      ≤ Ctwo * ((Real.sqrt 2 * Real.sqrt (β * A)) * (Cfro * s) +
          (2 * Real.sqrt (β * A)) * (Centry * s)) := by
        apply mul_le_mul_of_nonneg_left _ hCtwo
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right h1 (by positivity)
        · exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * s * Real.sqrt (β * A) := by ring

/-- Absorption of the corrected two-term (min-dimension) Bernstein threshold into
the Lemma 6.6 coefficient scale, under the `λ` sample-size hypothesis, for a
coherence parameter `ν ≤ μ₁ max(√μ₀, μ₁)`. -/
lemma lnAbsorb (Ctwo Centry Cfro : ℝ) (hCtwo : 0 < Ctwo) (hCentry : 0 < Centry)
    (hCfro : 0 < Cfro) (β lam : ℝ) (hβ : 2 < β) (hlam : 1 ≤ lam)
    (n₁ n₂ r m : ℕ) (μ₀ μ₁ ν : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hν0 : 0 ≤ ν) (hνle : ν ≤ μ₁ * max (Real.sqrt μ₀) μ₁) (hμ₁ : 1 ≤ μ₁)
    (hmlow : (m : ℝ) ≥
      lam * μ₁ * max (Real.sqrt μ₀) μ₁ * (↑(max n₁ n₂)) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂)))) :
    Ctwo *
        (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            Real.sqrt (ν * (r : ℝ) / (↑(min n₁ n₂)))) +
        (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (ν * (r : ℝ) / (↑(min n₁ n₂))))) ≤
      (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt ((ν * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlam0 : 0 < lam := by linarith
  have hμ₁0 : 0 < μ₁ := by linarith
  have hβ0 : 0 < β := by linarith
  have hmax0 : 0 < max (Real.sqrt μ₀) μ₁ := lt_of_lt_of_le hμ₁0 (le_max_right _ _)
  have hNNm : ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
    rcases le_total n₁ n₂ with h | h
    · rw [max_eq_right h, min_eq_left h, mul_comm]
    · rw [max_eq_left h, min_eq_right h]
  have hN1 : 1 ≤ max n₁ n₂ := le_max_of_le_left hn₁
  have hNpos : (0 : ℝ) < ((max n₁ n₂ : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hNmpos : (0 : ℝ) < ((min n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast (lt_min hn₁ hn₂)
  have hL0 : 0 ≤ Real.log ((max n₁ n₂ : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  set N : ℝ := ((max n₁ n₂ : ℕ) : ℝ) with hN
  set Nm : ℝ := ((min n₁ n₂ : ℕ) : ℝ) with hNm
  set L : ℝ := Real.log N with hL
  set s : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hs
  have hs0 : 0 ≤ s := mul_nonneg hμ₁0.le (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hL0 with hL0' | hLpos
  · rw [← hL0']
    simp
  · have hmpos : (0 : ℝ) < m := by
      have h1 : 0 < lam * μ₁ * max (Real.sqrt μ₀) μ₁ * N * r * (β * L) := by positivity
      exact lt_of_lt_of_le h1 hmlow
    have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
    have hN0 : N ≠ 0 := hNpos.ne'
    have hNm0 : Nm ≠ 0 := hNmpos.ne'
    set A : ℝ := ν * N * r * L / m with hA
    have hA0 : 0 ≤ A := by positivity
    have hνlam : ν ≤ lam * μ₁ * max (Real.sqrt μ₀) μ₁ := by
      calc ν ≤ μ₁ * max (Real.sqrt μ₀) μ₁ := hνle
        _ = 1 * (μ₁ * max (Real.sqrt μ₀) μ₁) := by ring
        _ ≤ lam * (μ₁ * max (Real.sqrt μ₀) μ₁) :=
          mul_le_mul_of_nonneg_right hlam (by positivity)
        _ = lam * μ₁ * max (Real.sqrt μ₀) μ₁ := by ring
    have hνNrβL : ν * N * r * (β * L) ≤
        lam * μ₁ * max (Real.sqrt μ₀) μ₁ * N * r * (β * L) := by
      have hβL : 0 ≤ β * L := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hνlam hNpos.le) hr'.le) hβL
    have hβA : β * A ≤ 1 := by
      have : β * A = (ν * N * r * (β * L)) / m := by rw [hA]; ring
      rw [this, div_le_one hmpos]
      linarith
    have hX0 : 0 ≤ ((β + 2) * L) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by positivity
    have E1 : ((β + 2) * L) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (ν * r / Nm) = (β + 2) * A := by
      rw [hA, ← hNNm]
      field_simp
    have E2 : Real.sqrt (((β + 2) * L) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * Real.sqrt (ν * r / Nm)) =
        Real.sqrt ((β + 2) * A) * (Cfro * s) := by
      rw [← E1, Real.sqrt_mul hX0, hs]
      ring
    have E3 : (((β + 2) * L) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (ν * r / Nm)) =
        ((β + 2) * A) * (Centry * s) := by
      rw [← E1, hs]
      ring
    rw [E2, E3]
    calc Ctwo * (Real.sqrt ((β + 2) * A) * (Cfro * s) + ((β + 2) * A) * (Centry * s))
        ≤ (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * s * Real.sqrt (β * A) :=
          lnAbsorbCore Ctwo Centry Cfro s β A hCtwo.le hCentry.le hCfro.le hs0 hβ.le hA0 hβA
      _ = (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt ((ν * N * r * (β * L)) / m) := by
          rw [hs, show β * A = (ν * N * r * (β * L)) / m by rw [hA]; ring]
          ring

theorem solution :
    ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 1
                (C₁ * Real.rpow lam (-1))) ≥
          1 - c₁ * Real.rpow (↑(max n₁ n₂)) (-β) := by
  -- universal constants supplied by the platform theorems
  obtain ⟨Cdiag, cdiag, hCdiag, hcdiag, hdiag⟩ :=
    linear_neumann_diagonal_contribution_small_with_lambda
  obtain ⟨Cfixed, hCfixed, hfixed⟩ := fixed_matrix_centered_sampling_spectral_bound
  obtain ⟨Centry, hCentry, hentry⟩ :=
    linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
  obtain ⟨Cfro, hCfro, hfro⟩ :=
    linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
  obtain ⟨Cpoint, cpoint, hCpoint, hcpoint, hpoint⟩ :=
    linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
      Centry Cfro hCentry hCfro
  obtain ⟨Ctwo, ctwo, hCtwo, hctwo, htwo⟩ :=
    linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
      Cpoint cpoint Centry Cfro hCpoint hcpoint
  obtain ⟨Couter, couter, hCouter, hcouter, houter⟩ :=
    linear_neumann_off_diagonal_decoupled_from_coefficient_bound Cfixed hCfixed
  obtain ⟨Cdec, cdec, hCdec, hcdec, hdec⟩ := linear_neumann_off_diagonal_decoupling_transfer
  have hCcoef : 0 < Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry) := by positivity
  refine ⟨Cdiag + Cdec * (Couter * (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry))),
    cdiag + cdec * (couter + ctwo), by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmlow
  have hn₁' : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₂' : (0 : ℝ) < n₂ := by exact_mod_cast hn₂
  have hp0 : 0 ≤ (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hp1 : (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hm
  -- the reduced coherence parameter
  have hν1 : 1 ≤ min μ₀ (μ₁ ^ 2) := le_min hμ₀ (by nlinarith)
  have hνμ₀ : min μ₀ (μ₁ ^ 2) ≤ μ₀ := min_le_left _ _
  have hνμ₁ : min μ₀ (μ₁ ^ 2) ≤ μ₁ ^ 2 := min_le_right _ _
  have hA0ν : A0 S (min μ₀ (μ₁ ^ 2)) := lnA0_min S μ₀ μ₁ hn₁ hn₂ hr hμ₁ hA0 hA1
  have hνle : min μ₀ (μ₁ ^ 2) ≤ μ₁ * max (Real.sqrt μ₀) μ₁ := by
    refine le_trans hνμ₁ ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  have hL0 : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_max_of_le_left hn₁ : 1 ≤ max n₁ n₂))
  have hmlowν : (m : ℝ) ≥
      lam * μ₁ * max (Real.sqrt (min μ₀ (μ₁ ^ 2))) μ₁ * (↑(max n₁ n₂)) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂))) := by
    refine le_trans ?_ hmlow
    have hmax : max (Real.sqrt (min μ₀ (μ₁ ^ 2))) μ₁ ≤ max (Real.sqrt μ₀) μ₁ :=
      max_le_max (Real.sqrt_le_sqrt hνμ₀) le_rfl
    have h0 : 0 ≤ lam * μ₁ := by nlinarith
    have hβL : 0 ≤ β * Real.log (↑(max n₁ n₂) : ℝ) := mul_nonneg (by linarith) hL0
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax h0) (by positivity))
        (by positivity)) hβL
  -- fixed-matrix sampling estimate (Theorem 6.3) at the required sample size
  have hmQ : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower β lam n₁ n₂ r m μ₀ μ₁
      hβ hlam hn₁ hn₂ hr hμ₀ hμ₁ hmlow
  have hfixedX : ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (fun Omega1 =>
          CenteredSamplingSpectralBound Omega1 ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * entrySupNorm X)) ≥
        1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) :=
    fun X => hfixed β hβ n₁ n₂ m X hn₁ hn₂ hm hmQ
  -- the decoupled contribution as a centered fluctuation of the coefficient matrix
  have hident : ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
      linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
        centeredSamplingFluctuation Omega1 ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) :=
    fun Omega1 Omega2 =>
      linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation Omega1 Omega2 S _
  -- pointwise scalar Bernstein tails for the coefficient entries (with ν)
  have hpointw : ∀ w : Fin n₁ × Fin n₂,
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (fun Omega2 =>
          |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2| ≤
            Cpoint *
              (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Cfro * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (min μ₀ (μ₁ ^ 2) * (r : ℝ) / (↑(min n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Centry * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  (min μ₀ (μ₁ ^ 2) * (r : ℝ) / (↑(min n₁ n₂)))))) ≥
        1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w
    refine hpoint 0 β hβ n₁ n₂ r m M (min μ₀ (μ₁ ^ 2)) μ₁ S hn₁ hn₂ hr hm hν1 hμ₁ hA0ν hA1
      (by simp) w ?_ ?_ ?_
    · intro Omega2
      exact linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
        Omega2 S _ w
    · exact hentry n₁ n₂ r M (min μ₀ (μ₁ ^ 2)) μ₁ S hn₁ hn₂ hr hν1 hμ₁ hA0ν hA1 w
    · exact hfro n₁ n₂ r M (min μ₀ (μ₁ ^ 2)) μ₁ S hn₁ hn₂ hr hν1 hμ₁ hA0ν hA1 w
  -- uniform (entry-sup) two-term coefficient event
  have htwoev := htwo 0 β hβ n₁ n₂ r m M (min μ₀ (μ₁ ^ 2)) μ₁ S hn₁ hn₂ hr hm hν1 hμ₁ hA0ν hA1
    (by simp) hpointw
  -- absorb the two-term threshold into the Lemma 6.6 scale
  have habs := lnAbsorb Ctwo Centry Cfro hCtwo hCentry hCfro β lam hβ hlam n₁ n₂ r m μ₀ μ₁
    (min μ₀ (μ₁ ^ 2)) hn₁ hn₂ hr (by linarith) hνle hμ₁ hmlow
  have hcoefev : bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega2 =>
        LinearNeumannOffDiagonalCoefficientBound Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          ((Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt ((min μ₀ (μ₁ ^ 2) * (↑(max n₁ n₂)) * (r : ℝ) *
                (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
      1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) := by
    refine le_trans htwoev (lnEventMono _ hp0 hp1 _ _ ?_)
    intro Omega2 h
    unfold LinearNeumannOffDiagonalCoefficientBound at h ⊢
    exact le_trans h habs
  -- decoupled pair event
  have hpair := houter β lam hβ hlam n₁ n₂ r m M (min μ₀ (μ₁ ^ 2)) μ₁ S hn₁ hn₂ hr hm hν1 hμ₁
    hA0ν hA1 hmlowν hfixedX hident (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) ctwo hCcoef hctwo
    hcoefev
  -- decoupling transfer back to the original off-diagonal contribution
  have hoff := hdec S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    (Couter * (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry))) (couter + ctwo) β lam hp0 hp1
    (by positivity) (by positivity) hpair
  -- diagonal contribution
  have hdiagev := hdiag β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmlow
  -- combine
  exact linear_neumann_correction_from_diagonal_off_diagonal_bounds S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Cdiag
    (Cdec * (Couter * (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)))) cdiag
    (cdec * (couter + ctwo)) β lam hp0 hp1 hcdiag (by positivity) hdiagev hoff
