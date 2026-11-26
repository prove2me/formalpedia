-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_partialDeriv_comm_apply
-- name    : BKAR.BKARContDiff.partialDeriv_comm_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:02:53.39003+00:00
-- url     : https://prove2.me/theorems/be34af1f-d9e3-513c-9c9d-fc62ec96033e
-- title:
--   BKARCont Diff: partial Deriv comm apply
-- statement:
--   Under the global BKAR smoothness hypothesis, coordinate partial derivatives
--   commute pointwise. This is the analytic order-independence ingredient needed
--   to replace recursive ordered-sector mixed partials by the order-free forest
--   mixed partial.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L32-L114
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L32-L114

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.partialDeriv_comm_apply
    (hρ : BKARContDiff ρ) (e f : Edge V) (x : Edge V → ℝ) :
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) x =
      BKAR.partialDeriv f (BKAR.partialDeriv e ρ) x := by sorry
