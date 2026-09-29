-- Prove2me | solution 1 for flt5_zz5_kummer_pid_root
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T09:33:35.346732+00:00
-- url     : https://prove2.me/submissions/c206c8d3-2cc5-4aca-9e8d-1ad2bbcec9fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Theorems.Thm_flt5_zz5_beta_fifth_power
import Theorems.Thm_flt5_zz5_unit_norm_one

-- Sketch: flt5_zz5_kummer_pid_root
-- Goal: Given β:ZZ5 with N(β)=s^5 and hPID, find d:ZZ5 with N(d)^5=s^5.
--
-- Strategy (Kummer PID argument):
--   1. Child flt5_zz5_beta_fifth_power: β = (u:ZZ5)*d^5 for some unit u and d:ZZ5
--      (uses PID + coprimeness of β to its conjugates)
--   2. Child flt5_zz5_unit_norm_one: N(u)=1 for any unit u
--   3. N(β) = N(u)*N(d)^5 = 1*N(d)^5 = N(d)^5 = s^5

noncomputable section

abbrev ZZ5kr := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (β : ZZ5kr) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hPID : IsPrincipalIdealRing ZZ5kr) :
    ∃ d : ZZ5kr, (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  -- Step 1: β = u * d^5 for some unit u:ZZ5ˣ and d:ZZ5
  obtain ⟨u, d, hβd⟩ := flt5_zz5_beta_fifth_power a b s h_cop β hβ hPID
  -- Step 2: N(u) = 1 since u is a unit
  have hN_unit : Algebra.norm ℤ (u : ZZ5kr) = 1 := flt5_zz5_unit_norm_one u
  -- Step 3: N(β) = N(u)*N(d)^5 = N(d)^5
  refine ⟨d, ?_⟩
  have hmul : Algebra.norm ℤ β = Algebra.norm ℤ (u : ZZ5kr) * (Algebra.norm ℤ d) ^ 5 := by
    rw [hβd]
    simp only [map_mul, map_pow]
  rw [hN_unit, one_mul] at hmul
  linarith [hβ.symm.trans hmul]

end
