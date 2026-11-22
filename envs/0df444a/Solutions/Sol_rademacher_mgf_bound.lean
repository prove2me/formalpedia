-- Prove2me | solution 1 for rademacher_mgf_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:43.888901+00:00
-- url     : https://prove2.me/submissions/077a8a3e-2fae-4a11-800c-7f744bea87bb

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_cosh_le_exp_sq_half

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (ha : ∀ i, |a i| ≤ c) (t : ℝ) (_ht : 0 ≤ t) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ : SignVector m, Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
    Real.exp (t ^ 2 * c ^ 2 / (2 * m)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  -- Step 1: Normalize the exp argument as a Finset sum, then factor into a product
  have h_step1 : ∀ σ : SignVector m,
      Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) =
      ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / m) := by
    intro σ
    have h_sum : t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i)) =
        ∑ i : Fin m, (t * a i * boolToSign (σ i) / m) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1; ext i; ring
    rw [h_sum, Real.exp_sum]
  simp_rw [h_step1]
  -- Goal: (1/card) * ∑ σ, ∏ i, exp(t*a_i*σ_i/m) ≤ exp(t²c²/(2m))
  -- Step 2: Swap sum over σ and product over i
  -- ∑ σ : (Fin m → Bool), ∏ i, g i (σ i) = ∏ i, ∑ b, g i b
  rw [show ∑ σ : SignVector m, ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i) / ↑m) =
      ∏ i : Fin m, ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) from by
    rw [← Fintype.piFinset_univ (β := fun _ : Fin m => Bool)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (i : Fin m) (b : Bool) => Real.exp (t * a i * boolToSign b / ↑m))]
  -- Step 2b: Distribute (1/card) = (1 / 2)^m into the product
  have hcard_eq : (Fintype.card (SignVector m) : ℝ) = (2 : ℝ) ^ m := by
    simp_all
  have h_inv : (1 : ℝ) / (Fintype.card (SignVector m) : ℝ) = (1 / 2 : ℝ) ^ m := by
    rw [hcard_eq, one_div, one_div, inv_pow]
  rw [h_inv]
  have h_prod_const : ((1 / 2 : ℝ) ^ m : ℝ) = ∏ _i : Fin m, (1 / 2 : ℝ) := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_const, ← Finset.prod_mul_distrib]
  -- Goal: ∏ i, (1 / 2) * ∑ b, exp(t*a_i*boolToSign(b)/m) ≤ exp(t²c²/(2m))
  -- Step 3: Each factor ≤ exp((t*a_i/m)²/2)
  have h_factor_bound : ∀ i : Fin m,
      (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) ≤
      Real.exp ((t * a i / ↑m) ^ 2 / 2) := by
    intro i
    -- Show the sum equals exp(u) + exp(-u) where u = t * a i / m
    set u := t * a i / (↑m : ℝ) with hu_def
    have h_sum_eq : ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) =
        Real.exp u + Real.exp (-u) := by
      simp only [Fintype.sum_bool, boolToSign, ↓reduceIte, Bool.false_eq_true]
      congr 1
      · congr 1; rw [hu_def]; ring
      · congr 1; rw [hu_def]; ring
    rw [h_sum_eq]
    -- (1 / 2) * (exp(u) + exp(-u)) = cosh(u) ≤ exp(u²/2)
    have h_eq_cosh : (1 / 2 : ℝ) * (Real.exp u + Real.exp (-u)) = Real.cosh u := by
      rw [Real.cosh_eq]; ring
    rw [h_eq_cosh]
    exact cosh_le_exp_sq_half _
  -- Each factor is nonneg
  have h_factor_nonneg : ∀ i ∈ Finset.univ (α := Fin m),
      0 ≤ (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m) := by
    intro i _
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg; intro b _; exact (Real.exp_pos _).le
  -- Step 4: Product inequality → exponential sum → final bound
  calc ∏ i : Fin m, (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b / ↑m)
      ≤ ∏ i : Fin m, Real.exp ((t * a i / ↑m) ^ 2 / 2) :=
        Finset.prod_le_prod h_factor_nonneg (fun i _ => h_factor_bound i)
    _ = Real.exp (∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2) :=
        (Real.exp_sum Finset.univ _).symm
    _ ≤ Real.exp (t ^ 2 * c ^ 2 / (2 * ↑m)) := by
        apply Real.exp_le_exp_of_le
        -- ∑ (t*a_i/m)²/2 = t²/(2m²) * ∑ a_i² ≤ t²/(2m²) * m*c² = t²c²/(2m)
        have h_sum_eq : ∑ i : Fin m, (t * a i / ↑m) ^ 2 / 2 =
            t ^ 2 / (2 * ↑m ^ 2) * ∑ i : Fin m, a i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [h_sum_eq]
        have h_sum_sq_le : ∑ i : Fin m, a i ^ 2 ≤ ↑m * c ^ 2 := by
          calc ∑ i : Fin m, a i ^ 2
              ≤ ∑ _i : Fin m, c ^ 2 := by
                apply Finset.sum_le_sum; intro i _
                exact sq_le_sq' (abs_le.mp (ha i)).1 (abs_le.mp (ha i)).2
            _ = ↑m * c ^ 2 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        calc t ^ 2 / (2 * ↑m ^ 2) * ∑ i : Fin m, a i ^ 2
            ≤ t ^ 2 / (2 * ↑m ^ 2) * (↑m * c ^ 2) := by
              apply mul_le_mul_of_nonneg_left h_sum_sq_le; positivity
          _ = t ^ 2 * c ^ 2 / (2 * ↑m) := by field_simp
