-- Prove2me | Theorems.Thm_DedekindZeta_Theta_traceForm_sub_left
-- name    : DedekindZeta.Theta.traceForm_sub_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:13:11.196203+00:00
-- url     : https://prove2.me/theorems/aee1f072-f880-4aee-9573-9657dad5d7c7
-- title:
--   Theta: trace Form sub left
-- statement:
--   `traceForm K η` is additive (here: respects subtraction) in its `K_ℝ`
--   argument. Used to compare `η` with `mixedEmbedding K b` in the fullness
--   argument.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L637-L641
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L637-L641

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.traceForm_sub_left (η η' : mixedSpace K) (a : K) :
    traceForm K (η - η') a = traceForm K η a - traceForm K η' a := by sorry
