-- Prove2me | Theorems.Thm_DiffContOnCl_dslope_of_mem_isOpen
-- name    : DiffContOnCl.dslope_of_mem_isOpen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:54.678692+00:00
-- url     : https://prove2.me/theorems/f0ceb748-0aaa-4763-b469-7ce43076bd05
-- title:
--   Diff Cont On Cl: dslope of mem is Open
-- statement:
--   The divided difference of a `DiffContOnCl` scalar function, filled in by
--   the derivative at an interior point, is again `DiffContOnCl`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L19-L28
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L19-L28

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem DiffContOnCl.dslope_of_mem_isOpen
    {U : Set ℂ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f U)
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    DiffContOnCl ℂ (dslope f z) U := by sorry
