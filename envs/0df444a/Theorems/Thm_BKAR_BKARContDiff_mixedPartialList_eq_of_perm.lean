-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_eq_of_perm
-- name    : BKAR.BKARContDiff.mixedPartialList_eq_of_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:23.140679+00:00
-- url     : https://prove2.me/theorems/29a42838-3f36-4819-b54f-7c780aae3e0f
-- title:
--   BKARCont Diff: mixed Partial List eq of perm
-- statement:
--   Mixed partials along two permuted edge lists agree under `BKARContDiff`.
--   This is the global analytic bridge from canonical-order expressions to the
--   unordered forest-edge derivative in the final cube contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L134-L151
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L134-L151

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

theorem BKAR.BKARContDiff.mixedPartialList_eq_of_perm
    {es₁ es₂ : List (Edge V)} (hperm : es₁.Perm es₂)
    (hρ : BKARContDiff ρ) :
    BKAR.mixedPartialList es₁ ρ =
      BKAR.mixedPartialList es₂ ρ := by sorry
