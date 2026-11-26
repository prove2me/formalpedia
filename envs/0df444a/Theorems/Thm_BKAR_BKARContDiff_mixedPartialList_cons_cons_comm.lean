-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_cons_cons_comm
-- name    : BKAR.BKARContDiff.mixedPartialList_cons_cons_comm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:03:01.014983+00:00
-- url     : https://prove2.me/theorems/fd8b4c8b-bff6-4431-a192-73dee7435485
-- title:
--   BKARCont Diff: mixed Partial List cons cons comm
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List cons cons comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L123-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L123-L127

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

theorem BKAR.BKARContDiff.mixedPartialList_cons_cons_comm
    (hρ : BKARContDiff ρ) (e f : Edge V) (es : List (Edge V)) :
    BKAR.mixedPartialList (e :: f :: es) ρ =
      BKAR.mixedPartialList (f :: e :: es) ρ := by sorry
