-- Prove2me | solution 1 for crazy7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:55.872823+00:00
-- url     : https://prove2.me/submissions/fcc93323-9442-41b3-acb4-5a07a31af6be

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven

set_option autoImplicit false
@[expose] public section
public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
theorem _root_.solution : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      (4 : ℝ) ≤ (4 / 3.15) ^ 3 * (6! / 6 ^ 6 * 129) := by norm_num
      _ ≤ (4 / π) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr
        · exact pi_lt_d2.le
        · exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  · calc
      (4 / π) ^ 3 * (6! / 6 ^ 6 * √16807) ≤ (4 / 3) ^ 3 * (6! / 6 ^ 6 * 130) := by
        gcongr
        · exact pi_gt_three.le
        · exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ < _ := by norm_num
