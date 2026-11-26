-- Prove2me | solution 1 for sqrt_mul_sqrt_le_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:09.936563+00:00
-- url     : https://prove2.me/submissions/a905738e-b393-4ef8-b2c4-72466373a627

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound

set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < s) :
    Real.sqrt A * Real.sqrt B ≤ (s * A + B / s) / 2 := by
  have h1 : Real.sqrt A * Real.sqrt B = Real.sqrt (s * A) * Real.sqrt (B / s) := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [h1]
  have hu := Real.sq_sqrt (by positivity : 0 ≤ s * A)
  have hv := Real.sq_sqrt (by positivity : 0 ≤ B / s)
  nlinarith only [sq_nonneg (Real.sqrt (s * A) - Real.sqrt (B / s)), hu, hv]
