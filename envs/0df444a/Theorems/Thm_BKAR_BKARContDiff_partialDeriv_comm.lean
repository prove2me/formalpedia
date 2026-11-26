-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_partialDeriv_comm
-- name    : BKAR.BKARContDiff.partialDeriv_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:58.357656+00:00
-- url     : https://prove2.me/theorems/1a8fdd07-8a30-45b7-8ec2-d1115a86c7ff
-- title:
--   BKARCont Diff: partial Deriv comm
-- statement:
--   The BKARCont Diff construction uses the partial Deriv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L116-L121
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L116-L121

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

theorem BKAR.BKARContDiff.partialDeriv_comm
    (hρ : BKARContDiff ρ) (e f : Edge V) :
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) =
      BKAR.partialDeriv f (BKAR.partialDeriv e ρ) := by sorry
