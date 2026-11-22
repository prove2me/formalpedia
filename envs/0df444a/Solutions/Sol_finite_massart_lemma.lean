-- Prove2me | solution 1 for finite_massart_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:29.103999+00:00
-- url     : https://prove2.me/submissions/68dabc2b-1f1b-43fc-bce2-258abea4a151

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_P2M_exp_mul_sup__le_sum_07b6ab8eda1c

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {m : ℕ} (_hm : 0 < m) {N : ℕ} (hN : 0 < N)
    (Z : Fin N → SignVector m → ℝ) (σ_param : ℝ) (hσ : 0 < σ_param)
    (h_mgf : ∀ j t, 0 ≤ t →
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
      Real.exp (t ^ 2 * σ_param ^ 2 / 2)) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv) ≤
    σ_param * Real.sqrt (2 * Real.log N) := by
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  -- Abbreviation for the LHS (the "expected maximum")
  set E_max := (1 / (Fintype.card (SignVector m) : ℝ)) *
    ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv)
  -- Card of SignVector m is positive (= 2^m > 0)
  have hcard_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := SignVector m)
  have hcard_ne : (Fintype.card (SignVector m) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
  -- Step A: For all t > 0, exp(t * E_max) ≤ N * exp(t²σ²/2)
  have h_exp_bound : ∀ t : ℝ, 0 < t →
      Real.exp (t * E_max) ≤ ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
    intro t ht
    -- A1: Jensen for convex exp with uniform weights 1/|SV|
    have h_jensen : Real.exp (t * E_max) ≤
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
            (fun j => Z j sv)) := by
      have h_weights_pos : ∀ sv ∈ Finset.univ (α := SignVector m),
          (0 : ℝ) ≤ 1 / (Fintype.card (SignVector m) : ℝ) :=
        fun _ _ => le_of_lt h1card_pos
      have h_weights_sum : ∑ _ : SignVector m, (1 / (Fintype.card (SignVector m) : ℝ)) = 1 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h_mem : ∀ sv ∈ Finset.univ (α := SignVector m),
          t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv) ∈ Set.univ :=
        fun _ _ => Set.mem_univ _
      have h_conv := convexOn_exp.map_sum_le (t := Finset.univ)
        (w := fun _ => 1 / (Fintype.card (SignVector m) : ℝ))
        (p := fun sv => t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv))
        h_weights_pos h_weights_sum h_mem
      simp only [smul_eq_mul] at h_conv
      -- h_conv: exp(∑ w * p) ≤ ∑ w * exp(p)
      -- RHS = ∑ (1/card * exp(...)) = (1/card) * ∑ exp(...)
      rw [Finset.mul_sum]
      -- Now goal: exp(t * E_max) ≤ ∑ (1/card * exp(...))
      -- Suffices: t * E_max = ∑ (1/card * (t * sup'))
      refine le_trans ?_ h_conv
      apply le_of_eq; congr 1
      simp only [E_max, ← Finset.mul_sum]; ring
    -- A2: Softmax for each σ
    have h_softmax : ∀ sv : SignVector m,
        Real.exp (t * Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv)) ≤
          ∑ j : Fin N, Real.exp (t * Z j sv) := by
      intro sv
      exact exp_mul_sup'_le_sum Finset.univ Finset.univ_nonempty
        (fun j => Z j sv) t (le_of_lt ht)
    -- A3: Swap sums and apply MGF bound
    have h_swap : (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, ∑ j : Fin N, Real.exp (t * Z j sv) =
        ∑ j : Fin N, (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    have h_mgf_applied : ∑ j : Fin N,
        (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
        ∑ _ : Fin N, Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact h_mgf j t (le_of_lt ht)
    have h_const_sum : ∑ _ : Fin N, Real.exp (t ^ 2 * σ_param ^ 2 / 2) =
        ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- Chain everything
    calc Real.exp (t * E_max)
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
              (fun j => Z j sv)) := h_jensen
      _ ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, ∑ j, Real.exp (t * Z j sv) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt h1card_pos)
          exact Finset.sum_le_sum (fun sv _ => h_softmax sv)
      _ = ∑ j, (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ sv, Real.exp (t * Z j sv) := h_swap
      _ ≤ ∑ _, Real.exp (t ^ 2 * σ_param ^ 2 / 2) := h_mgf_applied
      _ = ↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2) := h_const_sum
  -- Step B: For all t > 0: E_max ≤ log N / t + t * σ² / 2
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have h_linear_bound : ∀ t : ℝ, 0 < t →
      E_max ≤ Real.log N / t + t * σ_param ^ 2 / 2 := by
    intro t ht
    have h_exp := h_exp_bound t ht
    -- Take log: t * E_max ≤ log(N * exp(t²σ²/2)) = log N + t²σ²/2
    have h_log : t * E_max ≤ Real.log N + t ^ 2 * σ_param ^ 2 / 2 := by
      have h1 : t * E_max ≤ Real.log (↑N * Real.exp (t ^ 2 * σ_param ^ 2 / 2)) := by
        rw [← Real.log_exp (t * E_max)]
        exact Real.log_le_log (Real.exp_pos _) h_exp
      rw [Real.log_mul (ne_of_gt hN_pos) (ne_of_gt (Real.exp_pos _)),
          Real.log_exp] at h1
      exact h1
    -- Divide by t: E_max ≤ (log N + t²σ²/2) / t = log N / t + tσ²/2
    have ht_ne : t ≠ 0 := ne_of_gt ht
    rw [div_add_div _ _ ht_ne (ne_of_gt (by positivity : (0:ℝ) < 2))]
    rw [le_div_iff₀ (mul_pos ht (by positivity : (0:ℝ) < 2))]
    nlinarith [sq_nonneg t]
  -- Step C: Optimize over t
  have hlog_N_nonneg : 0 ≤ Real.log ↑N := Real.log_natCast_nonneg N
  have h2log_nonneg : 0 ≤ 2 * Real.log ↑N := by linarith
  by_cases hlog : Real.log ↑N = 0
  · -- N = 1 case: RHS = σ * √(2 * 0) = 0
    simp only [hlog, mul_zero, Real.sqrt_zero, mul_zero]
    -- Need: E_max ≤ 0. From bound: ∀ t > 0, E_max ≤ 0/t + tσ²/2 = tσ²/2
    -- By contradiction: if E_max > 0, choose t = E_max/σ² to get E_max ≤ E_max/2
    by_contra h_neg
    push Not at h_neg
    have hσ2_pos : 0 < σ_param ^ 2 := sq_pos_of_pos hσ
    set t₀ := E_max / σ_param ^ 2 with ht₀_def
    have ht₀_pos : 0 < t₀ := div_pos h_neg hσ2_pos
    have h_bd := h_linear_bound t₀ ht₀_pos
    rw [hlog] at h_bd
    simp only [zero_div, zero_add] at h_bd
    -- h_bd : E_max ≤ t₀ * σ² / 2 = (E_max / σ²) * σ² / 2 = E_max / 2
    have : t₀ * σ_param ^ 2 / 2 = E_max / 2 := by
      rw [ht₀_def]; field_simp
    rw [this] at h_bd
    linarith
  · -- N ≥ 2 case: log N > 0
    have hlog_pos : 0 < Real.log ↑N := lt_of_le_of_ne hlog_N_nonneg (Ne.symm hlog)
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.log ↑N) :=
      Real.sqrt_pos_of_pos (by linarith)
    -- Set t = √(2 log N) / σ
    set t₀ := Real.sqrt (2 * Real.log ↑N) / σ_param
    have ht₀_pos : 0 < t₀ := div_pos hsqrt_pos hσ
    have h_bd := h_linear_bound t₀ ht₀_pos
    -- Show: log N / t₀ + t₀ * σ² / 2 = σ * √(2 log N)
    suffices h_eq : Real.log ↑N / t₀ + t₀ * σ_param ^ 2 / 2 =
        σ_param * Real.sqrt (2 * Real.log ↑N) from le_trans h_bd (le_of_eq h_eq)
    have hσ_ne : σ_param ≠ 0 := ne_of_gt hσ
    have hsqrt_ne : Real.sqrt (2 * Real.log ↑N) ≠ 0 := ne_of_gt hsqrt_pos
    have hsq : Real.sqrt (2 * Real.log ↑N) ^ 2 = 2 * Real.log ↑N := Real.sq_sqrt h2log_nonneg
    -- Both terms equal σ * √(2 log N) / 2, so their sum = σ * √(2 log N)
    -- Direct computation after unfolding t₀
    change Real.log ↑N / t₀ + t₀ * σ_param ^ 2 / 2 = σ_param * Real.sqrt (2 * Real.log ↑N)
    have ht₀_ne : t₀ ≠ 0 := ne_of_gt ht₀_pos
    -- Rewrite as: (2 * log N + t₀² * σ²) / (2 * t₀) = σ * √(2 log N)
    -- where t₀ = √(2 log N) / σ, so t₀² = 2 log N / σ²
    -- thus 2 * log N + (2 log N / σ²) * σ² = 2 * log N + 2 * log N = 4 * log N... wait that's wrong
    -- Actually: log N / t₀ + t₀ * σ² / 2
    -- = log N * σ / √(2 log N) + √(2 log N) * σ / 2
    -- Key: log N / √(2 log N) = √(2 log N) / 2 (since √(2 log N)² = 2 log N)
    -- So = σ * √(2 log N) / 2 + σ * √(2 log N) / 2 = σ * √(2 log N). ✓
    -- Prove via: multiply both sides by 2 * √(2 log N)
    have hsqrt_ne : Real.sqrt (2 * Real.log ↑N) ≠ 0 := ne_of_gt hsqrt_pos
    have h_mul_self : Real.sqrt (2 * Real.log ↑N) * Real.sqrt (2 * Real.log ↑N) =
        2 * Real.log ↑N := Real.mul_self_sqrt h2log_nonneg
    -- Step 1: log N / t₀ = log N * σ / √(2 log N) = σ * √(2 log N) / 2
    have h1 : Real.log ↑N / t₀ = σ_param * Real.sqrt (2 * Real.log ↑N) / 2 := by
      simp only [t₀]
      rw [div_div_eq_mul_div]
      -- Goal: log N * σ / √(2 log N) = σ * √(2 log N) / 2
      rw [div_eq_div_iff hsqrt_ne two_ne_zero]
      nlinarith
    -- Step 2: t₀ * σ² / 2 = σ * √(2 log N) / 2
    have h2 : t₀ * σ_param ^ 2 / 2 = σ_param * Real.sqrt (2 * Real.log ↑N) / 2 := by
      simp only [t₀]
      rw [div_mul_eq_mul_div, div_div]
      rw [div_eq_div_iff (mul_ne_zero hσ_ne two_ne_zero) two_ne_zero]
      ring
    rw [h1, h2]; ring
