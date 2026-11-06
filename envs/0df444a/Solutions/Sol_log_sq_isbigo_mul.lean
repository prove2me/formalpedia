-- Prove2me | solution 1 for log_sq_isbigo_mul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:29:23.938195+00:00
-- url     : https://prove2.me/submissions/f5b5b49d-c993-40ac-b8f8-28b3f6b0fcba

import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Real Filter Asymptotics

private theorem tendsto_mul_add_atTop_aux {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

private theorem isLittleO_const_of_tendsto_atTop_aux {α : Type*} [Preorder α] (a : ℝ)
    {f : α → ℝ} (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

private theorem isLittleO_mul_add_sq_aux (a b : ℝ) :
    (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left
    simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop_aux _ <| tendsto_pow_atTop (by linarith)

private theorem log_mul_add_isBigO_log_aux {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop_aux ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b :=
    tendsto_atTop.mp (tendsto_mul_add_atTop_aux ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq_aux a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

private theorem isBigO_log_mul_add_aux {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log_aux (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop_aux (b := b) ha) using 1
  · ext x
    simp only [Function.comp_apply]
    congr
    field_simp
    simp
  · rfl

private theorem log_isBigO_log_div_aux {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add_aux (inv_pos.mpr hb) 0 using 1
  simp only [add_zero]
  field_simp

private theorem IsBigO.add_isLittleO_right_aux {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  exact h.right_isBigO_add'

private theorem IsBigO.sq_aux {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) :=
  h.pow 2

theorem solution {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (IsBigO.sq_aux (log_isBigO_log_div_aux hb)).trans
  simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right_aux <| isLittleO_const_of_tendsto_atTop_aux _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
