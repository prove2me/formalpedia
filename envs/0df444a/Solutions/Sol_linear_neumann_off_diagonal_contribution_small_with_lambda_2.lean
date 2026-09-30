-- Prove2me | solution 2 for linear_neumann_off_diagonal_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T15:36:19.223079+00:00
-- url     : https://prove2.me/submissions/571c1aa4-2d63-42dd-b4b3-61c0fd6a4a46

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_linear_neumann_off_diagonal_decoupling_transfer
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_from_coefficient_bound
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation

open MatrixCompletion

open scoped BigOperators

/-! ### Leverage: the sign-matrix entry bound `A1` forces coherence `μ₁²` -/

lemma signMatrix_apply' {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂} (S : SVD M r)
    (i : Fin n₁) (j : Fin n₂) :
    signMatrix S i j = ∑ k, S.u k i * S.v k j := by
  simp [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]

lemma p2m_row_energy {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂} (S : SVD M r) (i : Fin n₁) :
    ∑ j, (signMatrix S i j) ^ 2 = ∑ k, (S.u k i) ^ 2 := by
  simp only [signMatrix_apply', sq]
  calc ∑ j, (∑ k, S.u k i * S.v k j) * (∑ l, S.u l i * S.v l j)
      = ∑ j, ∑ k, ∑ l, (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    _ = ∑ k, ∑ l, (S.u k i * S.u l i) * ∑ j, (S.v k j * S.v l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun l _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ k, ∑ l, (S.u k i * S.u l i) * (if k = l then 1 else 0) := by
        simp only [S.v_orthonormal]
    _ = ∑ k, S.u k i * S.u k i := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [Finset.sum_ite_eq]

lemma p2m_col_energy {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂} (S : SVD M r) (j : Fin n₂) :
    ∑ i, (signMatrix S i j) ^ 2 = ∑ k, (S.v k j) ^ 2 := by
  simp only [signMatrix_apply', sq]
  calc ∑ i, (∑ k, S.u k i * S.v k j) * (∑ l, S.u l i * S.v l j)
      = ∑ i, ∑ k, ∑ l, (S.v k j * S.v l j) * (S.u k i * S.u l i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    _ = ∑ k, ∑ l, (S.v k j * S.v l j) * ∑ i, (S.u k i * S.u l i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun l _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ k, ∑ l, (S.v k j * S.v l j) * (if k = l then 1 else 0) := by
        simp only [S.u_orthonormal]
    _ = ∑ k, S.v k j * S.v k j := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [Finset.sum_ite_eq]

lemma p2m_A1_implies_A0_sq {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂} (S : SVD M r) (μ₁ : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (h : A1 S μ₁) : A0 S (μ₁ ^ 2) := by
  have hn₁' : (n₁ : ℝ) ≠ 0 := by exact_mod_cast hn₁.ne'
  have hn₂' : (n₂ : ℝ) ≠ 0 := by exact_mod_cast hn₂.ne'
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : (0 : ℝ) ≤ (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hsq : ∀ i j, (signMatrix S i j) ^ 2 ≤ μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    intro i j
    have h1 := h i j
    have h2 : (signMatrix S i j) ^ 2 ≤ (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [mul_pow, Real.sq_sqrt hc] at h2
    exact h2
  constructor
  · unfold coherence
    have hbound : ∀ i, ∑ k, (S.u k i) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / n₁ := by
      intro i
      rw [← p2m_row_energy S i]
      calc ∑ j, (signMatrix S i j) ^ 2
          ≤ ∑ _j : Fin n₂, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
            Finset.sum_le_sum (fun j _ => hsq i j)
        _ = μ₁ ^ 2 * (r : ℝ) / n₁ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
    have hsup : (⨆ i : Fin n₁, ∑ k, (S.u k i) ^ 2) ≤ μ₁ ^ 2 * (r : ℝ) / n₁ := ciSup_le hbound
    have hpos : (0 : ℝ) ≤ (n₁ : ℝ) / r := by positivity
    calc (n₁ : ℝ) / r * (⨆ i : Fin n₁, ∑ k, (S.u k i) ^ 2)
        ≤ (n₁ : ℝ) / r * (μ₁ ^ 2 * (r : ℝ) / n₁) := mul_le_mul_of_nonneg_left hsup hpos
      _ = μ₁ ^ 2 := by field_simp
  · unfold coherence
    have hbound : ∀ j, ∑ k, (S.v k j) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / n₂ := by
      intro j
      rw [← p2m_col_energy S j]
      calc ∑ i, (signMatrix S i j) ^ 2
          ≤ ∑ _i : Fin n₁, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
            Finset.sum_le_sum (fun i _ => hsq i j)
        _ = μ₁ ^ 2 * (r : ℝ) / n₂ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
    have hsup : (⨆ j : Fin n₂, ∑ k, (S.v k j) ^ 2) ≤ μ₁ ^ 2 * (r : ℝ) / n₂ := ciSup_le hbound
    have hpos : (0 : ℝ) ≤ (n₂ : ℝ) / r := by positivity
    calc (n₂ : ℝ) / r * (⨆ j : Fin n₂, ∑ k, (S.v k j) ^ 2)
        ≤ (n₂ : ℝ) / r * (μ₁ ^ 2 * (r : ℝ) / n₂) := mul_le_mul_of_nonneg_left hsup hpos
      _ = μ₁ ^ 2 := by field_simp

/-! ### Monotonicity of the Bernoulli event probability -/

lemma p2m_bernoulliEventProb_mono {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E₁ E₂ : Finset (Fin n₁ × Fin n₂) → Prop) (h : ∀ Ω, E₁ Ω → E₂ Ω) :
    bernoulliEventProb p E₁ ≤ bernoulliEventProb p E₂ := by
  unfold bernoulliEventProb
  refine Finset.sum_le_sum (fun Ω _ => ?_)
  have hw : 0 ≤ bernoulliObservationWeight p Ω := by
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  by_cases h₁ : E₁ Ω
  · rw [if_pos h₁, if_pos (h Ω h₁)]
  · rw [if_neg h₁]
    split_ifs
    · exact hw
    · exact le_rfl

/-! ### Absorption of the two-term Bernstein threshold into the Lemma 6.6 scale -/

lemma p2m_absorb_two_term
    (Ctwo Cfro Centry μ₁ s β L p μ₀ μ₀' N mn r m : ℝ)
    (hCtwo : 0 < Ctwo) (hCfro : 0 < Cfro) (hCentry : 0 < Centry)
    (hμ₁ : 0 ≤ μ₁) (hs : 0 ≤ s) (hβ : 2 < β) (hL : 0 ≤ L)
    (hN : 0 < N) (hmn : 0 < mn) (hr : 0 < r) (hm : 0 < m)
    (hp : p = m / (mn * N))
    (hμ₀' : 0 ≤ μ₀') (hμ₀'μ₀ : μ₀' ≤ μ₀)
    (hx' : μ₀' * N * r * (β * L) ≤ m) :
    Ctwo * (Real.sqrt (((β + 2) * L) / p) * (Cfro * μ₁ * s * Real.sqrt (μ₀' * r / mn)) +
        (((β + 2) * L) / p) * (Centry * μ₁ * s * (μ₀' * r / mn))) ≤
      (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * μ₁ * s *
        Real.sqrt ((μ₀ * N * r * (β * L)) / m) := by
  have hp0 : 0 < p := by rw [hp]; positivity
  have hμ₀ : 0 ≤ μ₀ := le_trans hμ₀' hμ₀'μ₀
  have hβ0 : 0 ≤ β := by linarith
  have hβ2 : 0 ≤ β + 2 := by linarith
  have hm' : m ≠ 0 := hm.ne'
  have hmn' : mn ≠ 0 := hmn.ne'
  have hN' : N ≠ 0 := hN.ne'
  set a := ((β + 2) * L) / p with ha_def
  set b := μ₀' * r / mn with hb_def
  set x := (μ₀ * N * r * (β * L)) / m with hx_def
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hβ2 hL) hp0.le
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hμ₀' hr.le) hmn.le
  have hx0 : 0 ≤ x :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hμ₀ hN.le) hr.le) (mul_nonneg hβ0 hL)) hm.le
  have hx'0 : 0 ≤ (μ₀' * N * r * (β * L)) / m :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hμ₀' hN.le) hr.le) (mul_nonneg hβ0 hL)) hm.le
  have hx'1 : (μ₀' * N * r * (β * L)) / m ≤ 1 := by
    rw [div_le_one hm]; exact hx'
  have hLNr : 0 ≤ L * N * r / m := by positivity
  have hab : a * b = ((β + 2) * μ₀') * (L * N * r / m) := by
    rw [ha_def, hb_def, hp]
    field_simp
  have hab_le_2x : a * b ≤ 2 * x := by
    rw [hab, hx_def]
    have h1 : (β + 2) * μ₀' ≤ 2 * β * μ₀ := by nlinarith
    calc ((β + 2) * μ₀') * (L * N * r / m) ≤ (2 * β * μ₀) * (L * N * r / m) :=
          mul_le_mul_of_nonneg_right h1 hLNr
      _ = 2 * ((μ₀ * N * r * (β * L)) / m) := by ring
  have hab_le_2x' : a * b ≤ 2 * ((μ₀' * N * r * (β * L)) / m) := by
    rw [hab]
    have h1 : (β + 2) * μ₀' ≤ 2 * β * μ₀' := by nlinarith
    calc ((β + 2) * μ₀') * (L * N * r / m) ≤ (2 * β * μ₀') * (L * N * r / m) :=
          mul_le_mul_of_nonneg_right h1 hLNr
      _ = 2 * ((μ₀' * N * r * (β * L)) / m) := by ring
  have hx'x : (μ₀' * N * r * (β * L)) / m ≤ x := by
    rw [hx_def]
    have h0 : 0 ≤ N * r * (β * L) := mul_nonneg (mul_nonneg hN.le hr.le) (mul_nonneg hβ0 hL)
    have hnum : μ₀' * N * r * (β * L) ≤ μ₀ * N * r * (β * L) := by nlinarith
    exact div_le_div_of_nonneg_right hnum hm.le
  -- Frobenius part
  have hF : Real.sqrt a * Real.sqrt b ≤ Real.sqrt 2 * Real.sqrt x := by
    rw [← Real.sqrt_mul ha, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt hab_le_2x
  -- range part
  have hR : a * b ≤ 2 * Real.sqrt x := by
    set y := (μ₀' * N * r * (β * L)) / m with hy_def
    have hy1 : Real.sqrt y ≤ 1 := by
      calc Real.sqrt y ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hx'1
        _ = 1 := Real.sqrt_one
    have hyy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hx'0
    have hy_le : y ≤ Real.sqrt y := by nlinarith [Real.sqrt_nonneg y]
    have h2 : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hx'x
    linarith
  have e1 : Ctwo * (Real.sqrt a * (Cfro * μ₁ * s * Real.sqrt b) + a * (Centry * μ₁ * s * b)) =
      (Ctwo * Cfro * μ₁ * s) * (Real.sqrt a * Real.sqrt b) +
        (Ctwo * Centry * μ₁ * s) * (a * b) := by ring
  have e2 : (Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry)) * μ₁ * s * Real.sqrt x =
      (Ctwo * Cfro * μ₁ * s) * (Real.sqrt 2 * Real.sqrt x) +
        (Ctwo * Centry * μ₁ * s) * (2 * Real.sqrt x) := by ring
  rw [e1, e2]
  have hc1 : 0 ≤ Ctwo * Cfro * μ₁ * s := by positivity
  have hc2 : 0 ≤ Ctwo * Centry * μ₁ * s := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hF hc1) (mul_le_mul_of_nonneg_left hR hc2)

/-! ### Lemma 6.6 coefficient bound in the Lemma 4.5 sample regime -/

theorem p2m_coef_bound_lam :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
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
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
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
  refine ⟨Ctwo * (Real.sqrt 2 * Cfro + 2 * Centry), ctwo, by positivity, hctwo, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  -- effective coherence parameter
  set μ₀' := min μ₀ (μ₁ ^ 2) with hμ₀'_def
  have hA0' : A0 S μ₀' := by
    have h2 := p2m_A1_implies_A0_sq S μ₁ hn₁ hn₂ hr hA1
    exact ⟨le_min hA0.1 h2.1, le_min hA0.2 h2.2⟩
  have hμ₀'1 : 1 ≤ μ₀' := le_min hμ₀ (by nlinarith)
  have hμ₀'0 : 0 ≤ μ₀' := by linarith
  have hμ₀'μ₀ : μ₀' ≤ μ₀ := min_le_left _ _
  have hzero : (m : ℝ) ≥
      0 * max (max (μ₁ ^ 2) (Real.sqrt μ₀' * μ₁))
            (μ₀' * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
        * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) := by
    simp
  have huni := htwo 0 β hβ n₁ n₂ r m M μ₀' μ₁ S hn₁ hn₂ hr hm hμ₀'1 hμ₁ hA0' hA1 hzero
    (fun w =>
      hpoint 0 β hβ n₁ n₂ r m M μ₀' μ₁ S hn₁ hn₂ hr hm hμ₀'1 hμ₁ hA0' hA1 hzero w
        (fun Omega2 =>
          linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
            Omega2 S _ w)
        (hentry n₁ n₂ r M μ₀' μ₁ S hn₁ hn₂ hr hμ₀'1 hμ₁ hA0' hA1 w)
        (hfro n₁ n₂ r M μ₀' μ₁ S hn₁ hn₂ hr hμ₀'1 hμ₁ hA0' hA1 w))
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  refine le_trans huni (p2m_bernoulliEventProb_mono _ hp0 hp1 _ _ ?_)
  intro Omega2 hΩ
  unfold LinearNeumannOffDiagonalCoefficientBound at hΩ ⊢
  refine le_trans hΩ ?_
  -- arithmetic
  have hN1 : (1 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
    exact_mod_cast (le_max_of_le_left hn₁ : 1 ≤ max n₁ n₂)
  have hL : 0 ≤ Real.log ((max n₁ n₂ : ℕ) : ℝ) := Real.log_nonneg hN1
  have hNpos : (0 : ℝ) < ((max n₁ n₂ : ℕ) : ℝ) := by linarith
  have hmnpos : (0 : ℝ) < ((min n₁ n₂ : ℕ) : ℝ) := by
    exact_mod_cast (lt_min hn₁ hn₂ : 0 < min n₁ n₂)
  have hprod : ((min n₁ n₂ : ℕ) : ℝ) * ((max n₁ n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
    rcases le_total n₁ n₂ with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]; ring
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hp : (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) =
        (m : ℝ) / (((min n₁ n₂ : ℕ) : ℝ) * ((max n₁ n₂ : ℕ) : ℝ)) := by rw [hprod]
    have hK : μ₀' ≤ μ₁ * max (Real.sqrt μ₀) μ₁ := by
      rcases le_total μ₁ (Real.sqrt μ₀) with h | h
      · rw [max_eq_left h]
        calc μ₀' ≤ μ₁ ^ 2 := min_le_right _ _
          _ = μ₁ * μ₁ := sq μ₁
          _ ≤ μ₁ * Real.sqrt μ₀ := mul_le_mul_of_nonneg_left h (by linarith)
      · rw [max_eq_right h]
        have hμ₀0 : 0 ≤ μ₀ := by linarith
        calc μ₀' ≤ μ₀ := min_le_left _ _
          _ = Real.sqrt μ₀ * Real.sqrt μ₀ := (Real.mul_self_sqrt hμ₀0).symm
          _ ≤ μ₁ * μ₁ := mul_le_mul h h (Real.sqrt_nonneg _) (by linarith)
    have hNrL : 0 ≤ ((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ)) :=
      mul_nonneg (mul_nonneg hNpos.le (Nat.cast_nonneg _)) (mul_nonneg (by linarith) hL)
    have hKmax : 0 ≤ μ₁ * max (Real.sqrt μ₀) μ₁ :=
      mul_nonneg (by linarith) (le_max_of_le_right (by linarith))
    have hx' : μ₀' * ((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ)) ≤
        (m : ℝ) := by
      calc μ₀' * ((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ))
          = μ₀' * (((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ))) := by
            ring
        _ ≤ (μ₁ * max (Real.sqrt μ₀) μ₁) *
              (((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_right hK hNrL
        _ ≤ lam * ((μ₁ * max (Real.sqrt μ₀) μ₁) *
              (((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ)))) := by
            have h0 : 0 ≤ (μ₁ * max (Real.sqrt μ₀) μ₁) *
                (((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) * (β * Real.log ((max n₁ n₂ : ℕ) : ℝ))) :=
              mul_nonneg hKmax hNrL
            nlinarith
        _ = lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
              (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) := by ring
        _ ≤ (m : ℝ) := hsample
    exact p2m_absorb_two_term Ctwo Cfro Centry μ₁ (Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
      β (Real.log ((max n₁ n₂ : ℕ) : ℝ)) ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) μ₀ μ₀'
      ((max n₁ n₂ : ℕ) : ℝ) ((min n₁ n₂ : ℕ) : ℝ) (r : ℝ) (m : ℝ)
      hCtwo hCfro hCentry (by linarith) (Real.sqrt_nonneg _) hβ hL hNpos hmnpos
      (by exact_mod_cast hr) hmR hp hμ₀'0 hμ₀'μ₀ hx'

/-! ### Decoupled off-diagonal bound -/

theorem p2m_decoupled_bound_lam :
    ∃ Cdec cdec : ℝ, 0 < Cdec ∧ 0 < cdec ∧
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
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Cdec * Real.rpow lam (-1)) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Cfixed, hCfixed, hfixed⟩ := fixed_matrix_centered_sampling_spectral_bound
  obtain ⟨Couter, couter, hCouter, hcouter, houter⟩ :=
    linear_neumann_off_diagonal_decoupled_from_coefficient_bound Cfixed hCfixed
  obtain ⟨Ccoef, ccoef, hCcoef, hccoef, hcoef⟩ := p2m_coef_bound_lam
  refine ⟨Couter * Ccoef, couter + ccoef, by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  have hfix_sample : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower β lam n₁ n₂ r m μ₀ μ₁
      hβ hlam hn₁ hn₂ hr hμ₀ hμ₁ hsample
  exact houter β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
    (fun X => hfixed β hβ n₁ n₂ m X hn₁ hn₂ hm hfix_sample)
    (fun Omega1 Omega2 =>
      linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation Omega1 Omega2 S _)
    Ccoef ccoef hCcoef hccoef
    (hcoef β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample)

theorem solution :
    ∃ Coff coff : ℝ, 0 < Coff ∧ 0 < coff ∧
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
              spectralNorm
                (linearNeumannOffDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Coff * Real.rpow lam (-1)) ≥
          1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Cdecouple, cdecouple, hCdecouple, hcdecouple, htransfer⟩ :=
    linear_neumann_off_diagonal_decoupling_transfer
  obtain ⟨Cdec, cdec, hCdec, hcdec, hdec⟩ := p2m_decoupled_bound_lam
  refine ⟨Cdecouple * Cdec, cdecouple * cdec, by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  exact htransfer S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Cdec cdec β lam hp0 hp1 hCdec hcdec
    (hdec β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample)
