-- Prove2me | solution 1 for flt5_zz5_lam_dvd_numerator
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T09:38:27.203299+00:00
-- url     : https://prove2.me/submissions/2306bf19-d1d8-48b0-a8df-0fe191529a1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Theorems.Thm_flt5_zz5_lambda_dvd_five

-- Sketch: flt5_zz5_lam_dvd_numerator
-- Goal: (1-ζ) | (a+ζb) in ZZ5 when 5|(a+b) in ℤ
-- Strategy:
--   1. Child flt5_zz5_lambda_dvd_five: (1-ζ) | (5:ZZ5)
--   2. From h5sum: (5:ℤ) | (a+b), lift to (5:ZZ5) | (a+b:ZZ5)
--   3. Transitivity: (1-ζ) | (a+b:ZZ5)
--   4. Ring identity: a+ζb = (a+b) - (1-ζ)*b
--   5. dvd_sub: (1-ζ) | (a+ζb)

noncomputable section

abbrev ZZ5ld := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (a b : ℤ) (h5sum : (5 : ℤ) ∣ a + b)
    (ζ : ZZ5ld) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) :
    (1 - ζ) ∣ ((a : ZZ5ld) + ζ * (b : ZZ5ld)) := by
  -- Step 1: (1-ζ) | 5 in ZZ5 (from Phi_5(1)=5 product formula)
  have hlam5 : (1 - ζ) ∣ (5 : ZZ5ld) := flt5_zz5_lambda_dvd_five ζ hζ
  -- Step 2: 5 | (a+b) in ZZ5 (lifted from ℤ)
  obtain ⟨k, hk⟩ := h5sum
  have h5sum_ZZ5 : (5 : ZZ5ld) ∣ ((a : ZZ5ld) + b) :=
    ⟨k, by exact_mod_cast hk⟩
  -- Step 3: (1-ζ) | (a+b) in ZZ5 by transitivity
  have h_lam_ab : (1 - ζ) ∣ ((a : ZZ5ld) + b) := dvd_trans hlam5 h5sum_ZZ5
  -- Step 4: a+ζb = (a+b) - (1-ζ)*b by ring
  have heq : (a : ZZ5ld) + ζ * b = ((a : ZZ5ld) + b) - (1 - ζ) * b := by ring
  -- Step 5: (1-ζ) | (a+ζb) by dvd_sub
  rw [heq]
  exact dvd_sub h_lam_ab (dvd_mul_right (1 - ζ) _)

end
