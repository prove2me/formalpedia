-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T08:04:20.832037+00:00
-- url     : https://prove2.me/submissions/b15a8be8-02e1-42ac-b0a6-b27305fc68d4

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_last_index_distinct_bound_from_centered_and_mean_bounds
import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_quadratic_neumann_last_index_distinct_mean_as_off_diagonal_response
import Theorems.Thm_quadratic_neumann_last_index_distinct_response_operator_bound_min_dim
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_a0_implies_default_a1_parameter

open MatrixCompletion

/-!
# The `ω₁ = ω₂ ≠ ω₃` quadratic Neumann contribution is `O(λ^{-3/2})`

Split `ξ² = (1-2p)ξ + p(1-p)`.  The centered part is the platform theorem
`quadratic_neumann_last_index_distinct_centered_contribution_small_with_lambda`.
The mean part equals `(1-p) · R(p⁻¹(P_Ω - p I)(p⁻¹E))` where `R` is the
off-diagonal response operator (platform identity); `‖R‖ ≤ C μ₀ r / n_min`
(platform), the centered sampling fluctuation of the fixed matrix `p⁻¹E`
obeys the Theorem 6.3 spectral bound `C √(β n log n / p) ‖p⁻¹E‖_∞` with
probability `≥ 1 - n^{-β}` (platform), and `‖E‖_∞ ≤ μ₀ √r √(r/(n₁n₂))`
(Cauchy–Schwarz from A0, platform).  An explicit scale computation shows the
product is `≤ C λ^{-3/2}` under `m ≥ λ μ₀^{4/3} n r^{4/3} β log n`.
-/

theorem lid_rpow_four_thirds_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((4 : ℝ) / 3)) ^ 3 = x ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem lid_rpow_neg_three_halves_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-((3 : ℝ) / 2))) ^ 2 = (x ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

theorem lid_log_two_gt_069 : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- Spectral norm is absolutely homogeneous. -/
theorem lid_spectralNorm_smul {n1 n2 : ℕ} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

/-- Entry sup norm of `c • X` is bounded by `|c|` times a uniform entry bound. -/
theorem lid_entrySupNorm_smul_le {n1 n2 : ℕ} [Nonempty (Fin n1)] [Nonempty (Fin n2)]
    (c b : ℝ) (X : RealMatrix n1 n2) (hb : ∀ i j, |X i j| ≤ b) :
    entrySupNorm (c • X) ≤ |c| * b := by
  unfold entrySupNorm
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hb i j) (abs_nonneg c)

theorem lid_sq_identity (Cresp Cfix β L p μ₀ r N nmin m : ℝ) (hp : p = m / (N * nmin))
    (hN : 0 < N) (hnmin : 0 < nmin) (hm : 0 < m) (hr0 : 0 ≤ r) (hβL : 0 ≤ β * N * L) :
    (Cresp * μ₀ * (r / nmin) *
      (Cfix * Real.sqrt ((β * N * L) / p) *
        (p⁻¹ * (μ₀ * Real.sqrt r * Real.sqrt (r / (N * nmin)))))) ^ 2
      = (Cresp * Cfix) ^ 2 * (μ₀ ^ 4 * r ^ 4 * (β * L) * N ^ 3) / m ^ 3 := by
  have hppos : 0 < p := by rw [hp]; positivity
  have hsq1 : (Real.sqrt ((β * N * L) / p)) ^ 2 = (β * N * L) / p :=
    Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0
  have hsq3 : (Real.sqrt (r / (N * nmin))) ^ 2 = r / (N * nmin) :=
    Real.sq_sqrt (by positivity)
  have e1 : (Cresp * μ₀ * (r / nmin) *
      (Cfix * Real.sqrt ((β * N * L) / p) *
        (p⁻¹ * (μ₀ * Real.sqrt r * Real.sqrt (r / (N * nmin)))))) ^ 2
      = Cresp ^ 2 * μ₀ ^ 2 * (r / nmin) ^ 2 * Cfix ^ 2 * (Real.sqrt ((β * N * L) / p)) ^ 2
        * (p⁻¹) ^ 2 * μ₀ ^ 2 * (Real.sqrt r) ^ 2 * (Real.sqrt (r / (N * nmin))) ^ 2 := by
    ring
  rw [e1, hsq1, hsq2, hsq3, hp]
  field_simp

theorem lid_rhs_sq_identity (C lam : ℝ) (hlam : 0 < lam) :
    (C * lam ^ (-((3 : ℝ) / 2))) ^ 2 = C ^ 2 * (lam ^ 3)⁻¹ := by
  have e1 : (C * lam ^ (-((3 : ℝ) / 2))) ^ 2 = C ^ 2 * (lam ^ (-((3 : ℝ) / 2))) ^ 2 := by
    ring
  rw [e1, lid_rpow_neg_three_halves_sq hlam]

theorem lid_final_div_step (C X lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hgoal : lam ^ 3 * X ≤ m ^ 3) :
    C ^ 2 * X / m ^ 3 ≤ C ^ 2 * (lam ^ 3)⁻¹ := by
  have hmk : 0 < m ^ 3 := by positivity
  have hlam3 : 0 < lam ^ 3 := by positivity
  rw [div_le_iff₀ hmk]
  calc C ^ 2 * X = C ^ 2 * (lam ^ 3 * X) * (lam ^ 3)⁻¹ := by field_simp
    _ ≤ C ^ 2 * (m ^ 3) * (lam ^ 3)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hgoal (by positivity)
    _ = C ^ 2 * (lam ^ 3)⁻¹ * m ^ 3 := by ring

/-- The mean-part scale is `O(λ^{-3/2})` under the sample-size hypothesis. -/
theorem lid_mean_scale_bound (Cresp Cfix β L lam μ₀ r N nmin m p : ℝ)
    (hCresp : 0 < Cresp) (hCfix : 0 < Cfix) (hβ : 2 < β) (hL : Real.log 2 ≤ L)
    (hlam : 1 ≤ lam) (hμ : 1 ≤ μ₀) (hr : 1 ≤ r) (hN : 0 < N) (hnmin : 0 < nmin)
    (hm : lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) ≤ m)
    (hp : p = m / (N * nmin)) :
    Cresp * μ₀ * (r / nmin) *
      (Cfix * Real.sqrt ((β * N * L) / p) *
        (p⁻¹ * (μ₀ * Real.sqrt r * Real.sqrt (r / (N * nmin)))))
      ≤ Cresp * Cfix * lam ^ (-((3 : ℝ) / 2)) := by
  have hL69 : (0.69 : ℝ) < L := lt_of_lt_of_le lid_log_two_gt_069 hL
  have hL0 : 0 < L := by linarith
  have hβ0 : 0 < β := by linarith
  have hlam0 : 0 < lam := by linarith
  have hμ0 : 0 < μ₀ := by linarith
  have hr0 : 0 < r := by linarith
  have hm₀pos : 0 < lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L) := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le hm₀pos hm
  have hB : 0 ≤ Cresp * Cfix * lam ^ (-((3 : ℝ) / 2)) := by positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero hB
  rw [lid_sq_identity Cresp Cfix β L p μ₀ r N nmin m hp hN hnmin hmpos hr0.le (by positivity),
    lid_rhs_sq_identity (Cresp * Cfix) lam hlam0]
  apply lid_final_div_step (Cresp * Cfix) _ lam m hlam0 hmpos
  have hm3 : (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 3 ≤ m ^ 3 :=
    pow_le_pow_left₀ hm₀pos.le hm 3
  have hm₀3 : (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 3
      = lam ^ 3 * μ₀ ^ 4 * N ^ 3 * r ^ 4 * (β * L) ^ 3 := by
    rw [← lid_rpow_four_thirds_cube hμ0.le, ← lid_rpow_four_thirds_cube hr0.le]; ring
  have hβL : 1 ≤ β * L := by nlinarith
  have hkey : β * L ≤ (β * L) ^ 3 := by
    have := pow_le_pow_right₀ hβL (show 1 ≤ 3 by norm_num)
    simpa using this
  calc lam ^ 3 * (μ₀ ^ 4 * r ^ 4 * (β * L) * N ^ 3)
      ≤ lam ^ 3 * (μ₀ ^ 4 * r ^ 4 * (β * L) ^ 3 * N ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = lam ^ 3 * μ₀ ^ 4 * N ^ 3 * r ^ 4 * (β * L) ^ 3 := by ring
    _ = (lam * μ₀ ^ ((4 : ℝ) / 3) * N * r ^ ((4 : ℝ) / 3) * (β * L)) ^ 3 := by rw [hm₀3]
    _ ≤ m ^ 3 := hm3

/-! ## Degenerate case `n₁ = n₂ = 1` -/

theorem lid_contribution_zero_of_subsingleton {n1 n2 r : ℕ} {M : Matrix (Fin n1) (Fin n2) ℝ}
    [Subsingleton (Fin n1 × Fin n2)] (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : ℝ) : quadraticNeumannLastIndexDistinctContribution Omega S p = 0 := by
  unfold quadraticNeumannLastIndexDistinctContribution
  rw [Finset.sum_eq_zero]
  · simp
  intro w1 _
  rw [Finset.sum_eq_zero]
  intro w3 _
  rw [if_pos (Subsingleton.elim w1 w3)]

theorem lid_spectralNorm_zero {n1 n2 : ℕ} : spectralNorm (0 : RealMatrix n1 n2) = 0 := by
  simp [spectralNorm]

theorem lid_prod_eq_max_mul_min (n₁ n₂ : ℕ) :
    ((n₁ : ℝ) * (n₂ : ℝ)) = ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) := by
  rcases le_total n₁ n₂ with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]

/-! ## Main theorem -/

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                C * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ccent, ccent, hCcent, hccent, Hcent⟩ :=
    quadratic_neumann_last_index_distinct_centered_contribution_small_with_lambda
  obtain ⟨Cresp, hCresp, Hresp⟩ :=
    quadratic_neumann_last_index_distinct_response_operator_bound_min_dim
  obtain ⟨Cfix, hCfix, Hfix⟩ := fixed_matrix_centered_sampling_spectral_bound
  refine ⟨Ccent + Cresp * Cfix, ccent + 1, by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hlam0 : 0 < lam := by linarith
  have hNnonneg : (0 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) (-β) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlamneg_nonneg : (0 : ℝ) ≤ Real.rpow lam (-((3 : ℝ) / 2)) := Real.rpow_nonneg hlam0.le _
  -- the centered event has high probability
  have Hc := Hcent β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  by_cases hN1 : max n₁ n₂ = 1
  · -- degenerate case: a single entry, the contribution vanishes identically
    have h1 : n₁ = 1 := by omega
    have h2 : n₂ = 1 := by omega
    subst h1 h2
    have hzero : ∀ Omega : Finset (Fin 1 × Fin 1),
        spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S
          ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))) ≤
          (Ccent + Cresp * Cfix) * Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro Omega
      rw [lid_contribution_zero_of_subsingleton, lid_spectralNorm_zero]
      positivity
    have hmono := bernoulli_event_probability_mono ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))
      (fun Omega => spectralNorm
        (quadraticNeumannLastIndexDistinctCenteredContribution Omega S
          ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))) ≤ Ccent * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega => spectralNorm
        (quadraticNeumannLastIndexDistinctContribution Omega S
          ((m : ℝ) / ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ)))) ≤
          (Ccent + Cresp * Cfix) * Real.rpow lam (-((3 : ℝ) / 2)))
      hp0 hp1 (fun Omega _ => hzero Omega)
    have hcu := mul_le_mul_of_nonneg_right (show ccent ≤ ccent + 1 by linarith) hNnonneg
    linarith
  · -- main case: `max n₁ n₂ ≥ 2`
    have hN2nat : 2 ≤ max n₁ n₂ := by omega
    -- notation
    set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
    set N : ℝ := ((max n₁ n₂ : ℕ) : ℝ) with hN
    set nmin : ℝ := ((min n₁ n₂ : ℕ) : ℝ) with hnmin
    set L : ℝ := Real.log N with hL
    have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN2nat
    have hN0 : 0 < N := by linarith
    have hnmin0 : 0 < nmin := by
      rw [hnmin]; exact_mod_cast (lt_min hn₁ hn₂)
    have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hN2
    have hL0 : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
    have hμ0pos : 0 < μ₀ := by linarith
    have hm₀pos : 0 < lam * μ₀ ^ ((4 : ℝ) / 3) * N * (r : ℝ) ^ ((4 : ℝ) / 3) * (β * L) := by
      positivity
    have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hm₀pos hsample
    have hprod : ((n₁ : ℝ) * (n₂ : ℝ)) = N * nmin := lid_prod_eq_max_mul_min n₁ n₂
    have hp' : p = (m : ℝ) / (N * nmin) := by rw [hp, hprod]
    have hppos : 0 < p := by rw [hp']; positivity
    -- the sample size dominates `β N log N`
    have hmβ : (m : ℝ) ≥ β * N * L := by
      have h1 : (1 : ℝ) ≤ μ₀ ^ ((4 : ℝ) / 3) := Real.one_le_rpow hμ₀ (by norm_num)
      have h2 : (1 : ℝ) ≤ (r : ℝ) ^ ((4 : ℝ) / 3) := Real.one_le_rpow hr1 (by norm_num)
      have h3 : (1 : ℝ) ≤ lam * μ₀ ^ ((4 : ℝ) / 3) * (r : ℝ) ^ ((4 : ℝ) / 3) := by
        calc (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ lam * μ₀ ^ ((4 : ℝ) / 3) * (r : ℝ) ^ ((4 : ℝ) / 3) :=
            mul_le_mul (mul_le_mul hlam h1 (by norm_num) hlam0.le) h2 (by norm_num)
              (by positivity)
      have h4 : β * N * L ≤ lam * μ₀ ^ ((4 : ℝ) / 3) * N * (r : ℝ) ^ ((4 : ℝ) / 3) * (β * L) := by
        have hNβL : 0 ≤ N * (β * L) := by positivity
        calc β * N * L = 1 * (N * (β * L)) := by ring
          _ ≤ (lam * μ₀ ^ ((4 : ℝ) / 3) * (r : ℝ) ^ ((4 : ℝ) / 3)) * (N * (β * L)) :=
            mul_le_mul_of_nonneg_right h3 hNβL
          _ = lam * μ₀ ^ ((4 : ℝ) / 3) * N * (r : ℝ) ^ ((4 : ℝ) / 3) * (β * L) := by ring
      have hsample' : (m : ℝ) ≥ lam * μ₀ ^ ((4 : ℝ) / 3) * N * (r : ℝ) ^ ((4 : ℝ) / 3) * (β * L) :=
        hsample
      linarith
    -- the fixed matrix `Y = p⁻¹ E`
    set Y : Matrix (Fin n₁) (Fin n₂) ℝ := p⁻¹ • signMatrix S with hY
    have hA1' : A1 S (defaultA1Parameter μ₀ r) :=
      a0_implies_default_a1_parameter n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ0pos.le hA0
    have hYsup : entrySupNorm Y ≤ p⁻¹ * (μ₀ * Real.sqrt (r : ℝ) * Real.sqrt ((r : ℝ) / (N * nmin))) := by
      have : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
      have : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
      have := lid_entrySupNorm_smul_le (p⁻¹)
        (μ₀ * Real.sqrt (r : ℝ) * Real.sqrt ((r : ℝ) / (N * nmin))) (signMatrix S)
        (by
          intro i j
          have := hA1' i j
          rw [defaultA1Parameter, hprod] at this
          exact this)
      rw [abs_of_pos (inv_pos.mpr hppos)] at this
      exact this
    -- Theorem 6.3 event for the fixed matrix `Y`
    have HB := Hfix β hβ n₁ n₂ m Y hn₁ hn₂ hm hmβ
    -- intersection of the two good events
    have Hinter := bernoulli_event_intersection_probability_from_lower_bounds p ccent 1
      (Real.rpow N (-β))
      (fun Omega => spectralNorm
        (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
          Ccent * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega => CenteredSamplingSpectralBound Omega p Y
        (Cfix * Real.sqrt ((β * N * L) / p) * entrySupNorm Y))
      hp0 hp1 Hc HB
    -- on the intersection, the full contribution is small
    have hscale := lid_mean_scale_bound Cresp Cfix β L lam μ₀ (r : ℝ) N nmin (m : ℝ) p hCresp hCfix
      hβ hL2 hlam hμ₀ hr1 hN0 hnmin0 hsample hp'
    have hsub : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        (spectralNorm (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
            Ccent * Real.rpow lam (-((3 : ℝ) / 2)) ∧
          CenteredSamplingSpectralBound Omega p Y
            (Cfix * Real.sqrt ((β * N * L) / p) * entrySupNorm Y)) →
        spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
          (Ccent + Cresp * Cfix) * Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro Omega ⟨hcent, hB⟩
      have hmean : spectralNorm (quadraticNeumannLastIndexDistinctMeanContribution Omega S p) ≤
          Cresp * Cfix * Real.rpow lam (-((3 : ℝ) / 2)) := by
        rw [quadratic_neumann_last_index_distinct_mean_as_off_diagonal_response Omega S p,
          lid_spectralNorm_smul]
        have h1 := Hresp n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 (centeredSamplingFluctuation Omega p Y)
        have h2 : spectralNorm (centeredSamplingFluctuation Omega p Y) ≤
            Cfix * Real.sqrt ((β * N * L) / p) * entrySupNorm Y := hB
        have h1p : |1 - p| ≤ 1 := by
          rw [abs_of_nonneg (by linarith)]; linarith
        have hsqrt_nonneg : 0 ≤ Cfix * Real.sqrt ((β * N * L) / p) := by positivity
        have hcoef_nonneg : 0 ≤ Cresp * μ₀ * ((r : ℝ) / nmin) := by positivity
        have hnorm_nonneg : 0 ≤ spectralNorm
            (quadraticLastIndexDistinctOffDiagonalResponse S
              (centeredSamplingFluctuation Omega p Y)) := by
          unfold spectralNorm; exact norm_nonneg _
        calc |1 - p| * spectralNorm
              (quadraticLastIndexDistinctOffDiagonalResponse S
                (centeredSamplingFluctuation Omega p Y))
            ≤ 1 * spectralNorm
              (quadraticLastIndexDistinctOffDiagonalResponse S
                (centeredSamplingFluctuation Omega p Y)) :=
              mul_le_mul_of_nonneg_right h1p hnorm_nonneg
          _ = spectralNorm
              (quadraticLastIndexDistinctOffDiagonalResponse S
                (centeredSamplingFluctuation Omega p Y)) := one_mul _
          _ ≤ Cresp * μ₀ * ((r : ℝ) / nmin) *
                spectralNorm (centeredSamplingFluctuation Omega p Y) := h1
          _ ≤ Cresp * μ₀ * ((r : ℝ) / nmin) *
                (Cfix * Real.sqrt ((β * N * L) / p) * entrySupNorm Y) :=
              mul_le_mul_of_nonneg_left h2 hcoef_nonneg
          _ ≤ Cresp * μ₀ * ((r : ℝ) / nmin) *
                (Cfix * Real.sqrt ((β * N * L) / p) *
                  (p⁻¹ * (μ₀ * Real.sqrt (r : ℝ) * Real.sqrt ((r : ℝ) / (N * nmin))))) := by
              apply mul_le_mul_of_nonneg_left _ hcoef_nonneg
              exact mul_le_mul_of_nonneg_left hYsup hsqrt_nonneg
          _ ≤ Cresp * Cfix * lam ^ (-((3 : ℝ) / 2)) := hscale
          _ = Cresp * Cfix * Real.rpow lam (-((3 : ℝ) / 2)) := by rw [Real.rpow_eq_pow]
      exact quadratic_neumann_last_index_distinct_bound_from_centered_and_mean_bounds S Omega p
        Ccent (Cresp * Cfix) lam hcent hmean
    have hmono := bernoulli_event_probability_mono p _ _ hp0 hp1 hsub
    linarith
