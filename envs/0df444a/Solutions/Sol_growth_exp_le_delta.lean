-- Prove2me | solution 1 for growth_exp_le_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:14.222204+00:00
-- url     : https://prove2.me/submissions/6643e3bb-1982-4d2c-9bc2-d149e9caf0ec

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_pow_mul_exp_neg_le_factorial_div
public import Theorems.Thm_sum_choose_le_exp_pow

section
@[expose] public section
universe u v
open MeasureTheory ENNReal
private lemma growth_function_le_two_pow {X : Type u}
    (C : ConceptClass X Bool) (n : ℕ) :
    GrowthFunction X C n ≤ 2 ^ n := by
  unfold GrowthFunction
  by_cases h_empty : (Set.range fun (S : { S : Finset X // S.card = n }) =>
    ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard) = ∅
  · simp only [h_empty, csSup_empty]; exact Nat.zero_le _
  · -- Range is nonempty
    have h_ne : Set.Nonempty (Set.range fun (S : { S : Finset X // S.card = n }) =>
        ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard) :=
      Set.nonempty_iff_ne_empty.mpr h_empty
    apply csSup_le h_ne
    rintro _ ⟨S, rfl⟩
    let T : Finset X := (↑S : Finset X)
    let : Fintype ↥T := Finset.fintypeCoeSort T
    have hBound' : ({ f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } :
        Set (↥T → Bool)).ncard ≤ 2 ^ n := by
      calc ({ f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } :
              Set (↥T → Bool)).ncard
          ≤ Nat.card (↥T → Bool) := Set.ncard_le_card _
        _ = Nat.card Bool ^ Nat.card ↥T := Nat.card_fun
        _ = 2 ^ n := by simp [Nat.card_eq_fintype_card, Fintype.card_coe, T, S.prop]
    simpa [T] using hBound'
private lemma growth_exp_le_delta_large_v {X : Type u}
    (C : ConceptClass X Bool)
    (v : ℕ) (hv : 0 < v) (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m)
    (hvm : ¬ v ≤ 2 * m) :
    4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤ δ := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hv1_pos : (0 : ℝ) < ↑v + 1 := by positivity
  have hm_delta : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) ≤ ↑m * δ := by
    rwa [div_le_iff₀ hδ] at hm_bound
  have hfact_le : (↑((v + 1).factorial) : ℝ) ≤ (↑v + 1) ^ (v + 1) :=
    by exact_mod_cast Nat.factorial_le_pow (v + 1)
  have hm_pow_ge_1 : (1 : ℝ) ≤ ↑m ^ v := one_le_pow₀ (Nat.one_le_cast.mpr hm)
  have he_ge_1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp_pow_ge_1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) := one_le_pow₀ he_ge_1
  push Not at hvm
  have hvm' : 2 * m + 1 ≤ v := by omega
  have hgf_trivial : GrowthFunction X C (2 * m) ≤ 2 ^ (2 * m) :=
    growth_function_le_two_pow C (2 * m)
  set t := (↑m : ℝ) * ε ^ 2 / 8 with ht_def
  have ht_pos : 0 < t := by positivity
  have hTaylor : t ^ (v + 1) / ↑((v + 1).factorial) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t (le_of_lt ht_pos) (v + 1)
  have hTaylor2 : t ^ (v + 1) ≤ ↑((v + 1).factorial) * Real.exp t := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (v + 1)))).mp hTaylor
    linarith [mul_comm (Real.exp t) (↑((v + 1).factorial) : ℝ)]
  have hexp_le : Real.exp (-t) ≤ ↑((v + 1).factorial) / t ^ (v + 1) := by
    have hexp_t_pos := Real.exp_pos t
    have ht_pow_pos := pow_pos ht_pos (v + 1)
    rw [Real.exp_neg, le_div_iff₀ ht_pow_pos]
    calc (Real.exp t)⁻¹ * t ^ (v + 1) ≤ 1 * ↑((v + 1).factorial) := by
          rw [inv_mul_le_iff₀ hexp_t_pos, one_mul]
          linarith [hTaylor2]
      _ = ↑((v + 1).factorial) := one_mul _
  have hchain1 : 4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤
      4 * (2 : ℝ) ^ (2 * m) * (↑((v + 1).factorial) / t ^ (v + 1)) := by
    have hgf_cast : (↑(GrowthFunction X C (2 * m)) : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
      exact_mod_cast hgf_trivial
    rw [ht_def]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hgf_cast (by norm_num)) hexp_le
      (Real.exp_pos (-(↑m * ε ^ 2 / 8))).le (by positivity)
  suffices hchain2 : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) ≤ δ * t ^ (v + 1) by
    have ht_pow_pos := pow_pos ht_pos (v + 1)
    have hdiv : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) / t ^ (v + 1) ≤ δ := by
      exact div_le_of_le_mul₀ (le_of_lt ht_pow_pos) (le_of_lt hδ) hchain2
    have hrewrite : 4 * (2 : ℝ) ^ (2 * m) *
        (↑((v + 1).factorial) / t ^ (v + 1)) =
        4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) / t ^ (v + 1) := by
      rw [mul_div_assoc']
    linarith [hchain1, hrewrite, hdiv]
  rw [ht_def]
  have hm_delta_expand :
      (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) ≤ ↑m * δ * (ε ^ 2) ^ (v + 1) := by
    have := hm_delta
    rw [div_pow, div_le_iff₀ (pow_pos hε2 (v + 1))] at this
    linarith
  have h_pow_bound : 4 * (2 : ℝ) ^ (2 * m) * (8 : ℝ) ^ (v + 1) ≤
      (16 : ℝ) ^ (v + 1) := by
    have h_2_pow : 4 * (2 : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ (v + 1) := by
      have : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [this, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have : (16 : ℝ) ^ (v + 1) = (2 : ℝ) ^ (v + 1) * (8 : ℝ) ^ (v + 1) := by
      rw [show (16 : ℝ) = 2 * 8 from by norm_num, mul_pow]
    rw [this]
    exact mul_le_mul_of_nonneg_right h_2_pow (pow_nonneg (by norm_num) (v + 1))
  have hgoal_equiv : δ * (↑m * ε ^ 2 / 8) ^ (v + 1) =
      δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) / (8 : ℝ) ^ (v + 1) := by
    rw [div_pow]; ring
  rw [hgoal_equiv]
  rw [show 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) =
      (4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1)) /
      (8 : ℝ) ^ (v + 1) from by
    rw [mul_div_cancel_right₀]; exact pow_ne_zero _ (by norm_num)]
  rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0:ℝ) < 8) (v + 1))]
  have hstep1 : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1) ≤
      (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) := by
    calc 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1)
        = (4 * (2 : ℝ) ^ (2 * m) * (8 : ℝ) ^ (v + 1)) * ↑((v + 1).factorial) := by
          ring
      _ ≤ (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) :=
        mul_le_mul h_pow_bound hfact_le (Nat.cast_nonneg _) (by positivity)
  have hstep2 : (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) ≤
      (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v := by
    rw [mul_pow, mul_pow]
    have h1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) * ↑m ^ v :=
      one_le_mul_of_one_le_of_one_le hexp_pow_ge_1 hm_pow_ge_1
    have h16pos := pow_pos (show (0:ℝ) < 16 by norm_num) (v + 1)
    have hv1pos := pow_pos hv1_pos (v + 1)
    calc (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1)
        ≤ ((16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1)) *
            (Real.exp 1 ^ (v + 1) * ↑m ^ v) :=
          le_mul_of_one_le_right (mul_nonneg h16pos.le hv1pos.le) h1
      _ = (16 : ℝ) ^ (v + 1) * Real.exp 1 ^ (v + 1) *
          (↑v + 1) ^ (v + 1) * ↑m ^ v := by ring
  have hstep3 : (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v ≤
      δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) := by
    have hmul : ↑m ^ v * (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) ≤
        ↑m ^ v * (↑m * δ * (ε ^ 2) ^ (v + 1)) :=
      mul_le_mul_of_nonneg_left hm_delta_expand (pow_nonneg (Nat.cast_nonneg _) v)
    have hpow_eq : (↑m : ℝ) ^ (v + 1) = ↑m ^ v * ↑m := pow_succ (↑m : ℝ) v
    calc (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v
        = ↑m ^ v * (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) := by ring
      _ ≤ ↑m ^ v * (↑m * δ * (ε ^ 2) ^ (v + 1)) := hmul
      _ = δ * (↑m ^ v * ↑m) * (ε ^ 2) ^ (v + 1) := by ring
      _ = δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) := by rw [← hpow_eq]
  linarith [hstep1, hstep2, hstep3]
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u}
    (C : ConceptClass X Bool)
    (v : ℕ) (hv : 0 < v) (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hv_bound : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m) :
    4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤ δ ∧
    2 * Real.log 2 ≤ ↑m * ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hv_pos : (0 : ℝ) < ↑v := Nat.cast_pos.mpr hv
  have hv1_pos : (0 : ℝ) < ↑v + 1 := by linarith
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase_pos : 0 < 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 := by positivity
  have hm_real_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have he_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm_delta : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) ≤ ↑m * δ := by
    rwa [div_le_iff₀ hδ] at hm_bound
  have hv1_ge_2 : (2 : ℝ) ≤ ↑v + 1 := by
    have : (1 : ℝ) ≤ ↑v := Nat.one_le_cast.mpr hv; linarith
  have hfact_le : (↑((v + 1).factorial) : ℝ) ≤ (↑v + 1) ^ (v + 1) :=
    by exact_mod_cast Nat.factorial_le_pow (v + 1)
  have hm_pow_ge_1 : (1 : ℝ) ≤ ↑m ^ v := one_le_pow₀ (Nat.one_le_cast.mpr hm)
  have hexp_pow_ge_1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) := one_le_pow₀ (by linarith)
  constructor
  · -- Part 1: 4 * GF(C, 2m) * exp(-mε²/8) ≤ δ
    by_cases hvm : v ≤ 2 * m
    · -- Case A: v ≤ 2m — use Sauer-Shelah + sum_choose_le_exp_pow
      have hgf_exp : (GrowthFunction X C (2 * m) : ℝ) ≤
          (Real.exp 1 * ↑(2 * m) / ↑v) ^ v := by
        have h1 : (GrowthFunction X C (2 * m) : ℝ) ≤
            ↑(∑ i ∈ Finset.range (v + 1), (2 * m).choose i) :=
          Nat.cast_le.mpr (hv_bound (2 * m) hvm)
        have h2 := sum_choose_le_exp_pow v (2 * m) hv hvm
        calc (GrowthFunction X C (2 * m) : ℝ) ≤ _ := h1
          _ = ∑ i ∈ Finset.range (v + 1), ↑((2 * m).choose i) := by push_cast; rfl
          _ ≤ _ := h2
      set t := (↑m : ℝ) * ε ^ 2 / 8 with ht_def
      have ht_pos : 0 < t := by positivity
      have h_pow_exp : t ^ v * Real.exp (-t) ≤ ↑((v + 1).factorial) / t :=
        pow_mul_exp_neg_le_factorial_div ht_pos
      have h2m_eq : (↑(2 * m) : ℝ) = 16 * t / ε ^ 2 := by
        rw [ht_def]; field_simp; push_cast; ring
      set K := 16 * Real.exp 1 / (↑v * ε ^ 2) with hK_def
      have hK_pos : 0 < K := by rw [hK_def]; positivity
      have hgf_factor : (Real.exp 1 * ↑(2 * m) / ↑v) ^ v = K ^ v * t ^ v := by
        have : Real.exp 1 * ↑(2 * m) / ↑v = K * t := by
          rw [h2m_eq, hK_def, ht_def]
          have hv_ne : (↑v : ℝ) ≠ 0 := ne_of_gt hv_pos
          have hε2_ne : ε ^ 2 ≠ 0 := ne_of_gt hε2
          field_simp
        rw [this, mul_pow]
      have hB_eq : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 = K * ↑v * (↑v + 1) := by
        rw [hK_def]; field_simp
      have hCvv : K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) ≤ ↑m * δ := by
        rw [show K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) =
            (K * ↑v * (↑v + 1)) ^ (v + 1) from by rw [mul_pow, mul_pow], ← hB_eq]
        exact hm_delta
      have hv_pow_ge_1 : (1 : ℝ) ≤ ↑v ^ v :=
        one_le_pow₀ (Nat.one_le_cast.mpr hv)
      have h_2_le_ev : (2 : ℝ) ≤ Real.exp 1 * ↑v ^ v :=
        le_trans (by linarith) (mul_le_mul_of_nonneg_left hv_pow_ge_1 (Real.exp_pos 1).le)
      have hkey : 2 * ↑((v + 1).factorial) ≤
          Real.exp 1 * ↑v ^ v * (↑v + 1) ^ (v + 1) := by
        calc 2 * (↑((v + 1).factorial) : ℝ) ≤ 2 * (↑v + 1) ^ (v + 1) :=
              mul_le_mul_of_nonneg_left hfact_le (by norm_num)
          _ ≤ Real.exp 1 * ↑v ^ v * (↑v + 1) ^ (v + 1) :=
              mul_le_mul_of_nonneg_right h_2_le_ev (pow_nonneg hv1_pos.le _)
      have hKeps : K * ε ^ 2 * ↑v ^ (v + 1) = 16 * Real.exp 1 * ↑v ^ v := by
        have : K * (↑v * ε ^ 2) = 16 * Real.exp 1 := by
          rw [hK_def]
          field_simp
        calc K * ε ^ 2 * ↑v ^ (v + 1)
            = K * (↑v * ε ^ 2) * ↑v ^ v := by rw [pow_succ]; ring
          _ = 16 * Real.exp 1 * ↑v ^ v := by rw [this]
      have hstepA : 32 * ↑((v + 1).factorial) ≤
          K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) := by
        rw [hKeps]
        linarith only [hkey]
      have hstepB : K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v ≤
          ε ^ 2 * (↑m * δ) := by
        have : K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v =
            ε ^ 2 * (K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1)) := by
          rw [show K ^ (v + 1) = K ^ v * K from pow_succ K v]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hCvv hε2.le
      have hcombine : 32 * ↑((v + 1).factorial) * K ^ v ≤ δ * ↑m * ε ^ 2 := by
        calc 32 * ↑((v + 1).factorial) * K ^ v
            ≤ (K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1)) * K ^ v :=
              mul_le_mul_of_nonneg_right hstepA (pow_nonneg hK_pos.le v)
          _ = K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v := by ring
          _ ≤ ε ^ 2 * (↑m * δ) := hstepB
          _ = δ * ↑m * ε ^ 2 := by ring
      have hfinal : 4 * K ^ v * (↑((v + 1).factorial) / t) ≤ δ := by
        rw [ht_def, show 4 * K ^ v * (↑((v + 1).factorial) / (↑m * ε ^ 2 / 8)) =
            32 * ↑((v + 1).factorial) * K ^ v / (↑m * ε ^ 2) from by ring]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < ↑m * ε ^ 2)]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcombine
      calc 4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8))
          ≤ 4 * (K ^ v * t ^ v) * Real.exp (-t) := by
            have hscaled := mul_le_mul_of_nonneg_left (hgf_exp.trans hgf_factor.le)
              (show (0:ℝ) ≤ 4 by norm_num)
            simpa [ht_def, mul_assoc] using
              mul_le_mul_of_nonneg_right hscaled (Real.exp_pos (-t)).le
        _ = 4 * K ^ v * (t ^ v * Real.exp (-t)) := by ring
        _ ≤ 4 * K ^ v * (↑((v + 1).factorial) / t) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left h_pow_exp
              (show (0:ℝ) ≤ 4 * K ^ v from mul_nonneg (by norm_num) (pow_nonneg hK_pos.le v))
        _ ≤ δ := hfinal
    · exact growth_exp_le_delta_large_v C v hv m hm ε δ hε hδ hm_bound hvm
  · -- Part 2: 2 * log 2 ≤ m * ε²
    have hlog2_le_1 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]; linarith
    suffices h : 2 ≤ ↑m * ε ^ 2 by linarith only [h, hlog2_le_1]
    by_cases hcase : ε ^ 2 ≤ 16 * Real.exp 1 * (↑v + 1)
    · have hbase_ge_1 : 1 ≤ 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 := by
        rw [le_div_iff₀ hε2]; linarith
      have hpow_ge : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 ≤
          (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) :=
        le_self_pow₀ hbase_ge_1 (by omega)
      have : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 ≤ ↑m * δ := by linarith [hm_delta]
      have : 16 * Real.exp 1 * (↑v + 1) ≤ ↑m * δ * ε ^ 2 := by
        rwa [div_le_iff₀ hε2] at this
      have hconstant : (2 : ℝ) ≤ 16 * Real.exp 1 * (↑v + 1) := by
        calc (2 : ℝ) ≤ 16 * 2 * 2 := by norm_num
          _ ≤ 16 * Real.exp 1 * (↑v + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left he_ge_2 (by norm_num))
              hv1_ge_2 (by norm_num) (by positivity)
      have hscaled : (↑m : ℝ) * δ * ε ^ 2 ≤ ↑m * ε ^ 2 := by
        calc (↑m : ℝ) * δ * ε ^ 2 = (↑m * ε ^ 2) * δ := by ring
          _ ≤ (↑m * ε ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hδ1.le (by positivity)
          _ = ↑m * ε ^ 2 := mul_one _
      exact hconstant.trans (this.trans hscaled)
    · push Not at hcase
      have hm_ge_1 : (1 : ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm
      have hbase_ge_two : (2 : ℝ) ≤ 16 * Real.exp 1 * (↑v + 1) := by
        have hleft : (16 : ℝ) * 2 ≤ 16 * Real.exp 1 :=
          mul_le_mul_of_nonneg_left he_ge_2 (by norm_num)
        have hright : (16 : ℝ) * 2 * 2 ≤ (16 * Real.exp 1) * (↑v + 1) :=
          mul_le_mul hleft hv1_ge_2 (by norm_num) (by positivity)
        calc (2 : ℝ) ≤ 16 * 2 * 2 := by norm_num
          _ ≤ 16 * Real.exp 1 * (↑v + 1) := by simpa [mul_assoc] using hright
      have hε2_ge_two : (2 : ℝ) ≤ ε ^ 2 :=
        (lt_of_le_of_lt hbase_ge_two hcase).le
      exact le_trans hε2_ge_two
        (by simpa [one_mul] using mul_le_mul_of_nonneg_right hm_ge_1 hε2.le)
