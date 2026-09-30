-- Prove2me | solution 1 for syracuse_white_point_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:35:30.05036+00:00
-- url     : https://prove2.me/submissions/3658f398-470c-4987-afb1-5923c0b2c018

import Mathlib
import Definitions.Def_syracuseDyadicPhase
import Definitions.Def_positivePairSumThree
import Definitions.Def_positivePairCharacterAverage
set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators Classical

lemma wp7a_pair_ne : positivePair12 ≠ positivePair21 := by
  intro h
  have := congrFun h 0
  simp [positivePair12, positivePair21] at this

lemma wp7a_event_eq :
    positivePairSumThreeEvent = ({positivePair12} : Set (Fin 2 → ℕ)) ∪ {positivePair21} := by
  ext a
  simp only [positivePairSumThreeEvent, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    Fin.sum_univ_two, Fin.forall_fin_two]
  constructor
  · rintro ⟨⟨h0, h1⟩, hs⟩
    have hc : (a 0 = 1 ∧ a 1 = 2) ∨ (a 0 = 2 ∧ a 1 = 1) := by omega
    rcases hc with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · left; funext i; fin_cases i <;> simp [positivePair12, e0, e1]
    · right; funext i; fin_cases i <;> simp [positivePair21, e0, e1]
  · rintro (rfl | rfl) <;> simp [positivePair12, positivePair21]

lemma wp7a_avg {N : ℕ} [NeZero N] (x : ZMod N) :
    positivePairCharacterAverage x = 0 ∨
      positivePairCharacterAverage x =
        (1 / 2 : ℂ) * (ZMod.stdAddChar (x * 7) + ZMod.stdAddChar (x * 5)) := by
  set μ := positiveGeomTwoVector 2 with hμ
  have hm : μ.real ({positivePair12} : Set (Fin 2 → ℕ)) =
      μ.real ({positivePair21} : Set (Fin 2 → ℕ)) := by
    simp only [hμ, positiveGeomTwoVector, measureReal_def, Measure.pi_singleton,
      Fin.prod_univ_two, positivePair12, positivePair21]
    simp [mul_comm]
  have hE : μ.real positivePairSumThreeEvent =
      μ.real ({positivePair12} : Set (Fin 2 → ℕ)) + μ.real ({positivePair21} : Set (Fin 2 → ℕ)) := by
    rw [wp7a_event_eq]
    exact measureReal_union (Set.disjoint_singleton.2 wp7a_pair_ne) (measurableSet_singleton _)
  unfold positivePairCharacterAverage
  rw [← hμ, hE, positivePairSumThree, Finset.sum_pair wp7a_pair_ne, ← hm]
  set m := μ.real ({positivePair12} : Set (Fin 2 → ℕ))
  by_cases h0 : m = 0
  · left; simp [h0]
  · right
    have h7 : x * ((2 ^ (positivePair12 1) + 3 : ℕ) : ZMod N) = x * 7 := by
      simp [positivePair12]
    have h5 : x * ((2 ^ (positivePair21 1) + 3 : ℕ) : ZMod N) = x * 5 := by
      simp [positivePair21]
    rw [h7, h5]
    have hc : (m : ℂ) ≠ 0 := by exact_mod_cast h0
    field_simp
    push_cast
    ring

lemma wp7a_one_add {N : ℕ} [NeZero N] (y : ZMod N) :
    ‖1 + ZMod.stdAddChar y‖ =
      2 * |Real.cos (Real.pi * centeredPhase ((y.val : ℝ) / (N : ℝ)))| := by
  set u := centeredPhase ((y.val : ℝ) / (N : ℝ)) with hu
  set k := toIocDiv (show (0 : ℝ) < 1 by norm_num) (-(1 / 2 : ℝ)) ((y.val : ℝ) / (N : ℝ)) with hk
  have hv : (y.val : ℝ) / (N : ℝ) = u + (k : ℝ) := by
    have := toIocMod_add_toIocDiv_zsmul (show (0 : ℝ) < 1 by norm_num) (-(1 / 2 : ℝ))
      ((y.val : ℝ) / (N : ℝ))
    rw [zsmul_eq_mul, mul_one] at this
    rw [hu, hk, centeredPhase]
    linarith
  have hvC : ((y.val : ℂ) / (N : ℂ)) = (u : ℂ) + (k : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hv
    push_cast at this
    exact this
  have he : ZMod.stdAddChar y = Complex.exp ((2 * Real.pi * u : ℝ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    have : 2 * (Real.pi : ℂ) * Complex.I * (y.val : ℂ) / (N : ℂ) =
        ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [mul_div_assoc, hvC]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hfac : 1 + Complex.exp ((2 * Real.pi * u : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * u : ℝ) * Complex.I) * (2 * Complex.cos ((Real.pi * u : ℝ))) := by
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have h1 : ((Real.pi * u : ℝ) : ℂ) * Complex.I + ((Real.pi * u : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have h2 : ((Real.pi * u : ℝ) : ℂ) * Complex.I + -((Real.pi * u : ℝ) : ℂ) * Complex.I = 0 := by
      ring
    rw [h1, h2, Complex.exp_zero]; ring
  rw [he, hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_mul, ← Complex.ofReal_cos,
    Complex.norm_real, Real.norm_eq_abs]
  simp

lemma wp7a_real (u ε : ℝ) (hu1 : -(1 / 2 : ℝ) < u) (hu2 : u ≤ 1 / 2) (hε : 0 < ε)
    (hεs : ε < 1 / 100) (hw : ε < |u|) : |Real.cos (Real.pi * u)| ≤ Real.exp (-ε ^ 3) := by
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ Real.cos (Real.pi * u) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · nlinarith
    · nlinarith
  have habs : |Real.pi * u| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hpi]
    have : |u| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith
  have hq := Real.cos_le_one_sub_mul_cos_sq habs
  have hq' : Real.cos (Real.pi * u) ≤ 1 - 2 * u ^ 2 := by
    have : 2 / Real.pi ^ 2 * (Real.pi * u) ^ 2 = 2 * u ^ 2 := by
      field_simp
    linarith
  have hu2' : ε ^ 2 < u ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg u, neg_abs_le u]) hw
    simpa [sq_abs] using this
  have he := Real.add_one_le_exp (-ε ^ 3)
  rw [abs_of_nonneg hc0]
  nlinarith [pow_pos hε 2, pow_pos hε 3]

theorem solution (n : ℕ) (hn : 1 ≤ n) (ξ : ZMod (3 ^ n)) (hξ : IsUnit ξ) (j : ℕ) (hj : 1 ≤ j) (hjn : 2 * j ≤ n) (l : ℤ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < 1 / 100) (hwhite : ε < |centeredPhase (((syracuseDyadicPhase n ξ j l).val : ℝ) / (3 ^ n : ℝ))|) : ‖syracuseWhitePointAverage n ξ j l‖ ≤ Real.exp (-ε ^ 3) := by
  have : NeZero (3 ^ n) := ⟨by positivity⟩
  set P := syracuseDyadicPhase n ξ j l with hP
  set x : ZMod (3 ^ n) := -((2 : ZMod (3 ^ n))⁻¹ * P) with hx
  have hmem := toIocMod_mem_Ioc (show (0 : ℝ) < 1 by norm_num) (-(1 / 2 : ℝ))
    (((P.val : ℝ) / (3 ^ n : ℝ)))
  have hreal : |Real.cos (Real.pi * centeredPhase ((P.val : ℝ) / (3 ^ n : ℝ)))| ≤
      Real.exp (-ε ^ 3) := wp7a_real _ ε hmem.1 (by unfold centeredPhase; linarith [hmem.2]) hε hεsmall hwhite
  unfold syracuseWhitePointAverage
  rw [← hP, ← hx]
  rcases wp7a_avg x with h | h
  · rw [h, norm_zero]; exact (Real.exp_pos _).le
  · rw [h]
    have h2 : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
      have := ZMod.coe_mul_inv_eq_one (n := 3 ^ n) 2 ((by decide : Nat.Coprime 2 3).pow_right n)
      exact_mod_cast this
    have hx2 : x * 2 = -P := by
      rw [hx]; linear_combination (-P) * h2
    have hsplit : ZMod.stdAddChar (x * 7) + ZMod.stdAddChar (x * 5) =
        ZMod.stdAddChar (x * 5) * (ZMod.stdAddChar (-P) + 1) := by
      rw [← hx2, mul_add, mul_one, ← AddChar.map_add_eq_mul]
      ring_nf
    have hflip : ‖ZMod.stdAddChar (-P) + 1‖ = ‖1 + ZMod.stdAddChar P‖ := by
      have hprod : ZMod.stdAddChar P * ZMod.stdAddChar (-P) = (1 : ℂ) := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      have hn1 : ‖(ZMod.stdAddChar P : ℂ)‖ = 1 := by
        rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
      calc ‖ZMod.stdAddChar (-P) + 1‖
          = ‖ZMod.stdAddChar P‖ * ‖ZMod.stdAddChar (-P) + 1‖ := by rw [hn1, one_mul]
        _ = ‖ZMod.stdAddChar P * (ZMod.stdAddChar (-P) + 1)‖ := (norm_mul _ _).symm
        _ = ‖1 + ZMod.stdAddChar P‖ := by rw [mul_add, hprod, mul_one, add_comm]
    have hn5 : ‖(ZMod.stdAddChar (x * 5) : ℂ)‖ = 1 := by
      rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
    rw [hsplit, norm_mul, norm_mul, hn5, hflip, wp7a_one_add]
    have hcast : ((3 ^ n : ℕ) : ℝ) = (3 ^ n : ℝ) := by push_cast; ring
    rw [hcast]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
