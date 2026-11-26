-- Prove2me | Theorems.Thm_BKAR_Forest_apply_activeDirection_eq_activeEdgePartialSum
-- name    : BKAR.Forest.apply_activeDirection_eq_activeEdgePartialSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:21.766626+00:00
-- url     : https://prove2.me/theorems/98d0ceca-d769-4af9-8668-303bc9047b78
-- title:
--   Forest: apply active Direction eq active Edge Partial Sum
-- statement:
--   The Forest construction uses the apply active Direction eq active Edge Partial Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L244-L258
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L244-L258

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.apply_activeDirection_eq_activeEdgePartialSum (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    ρ' F.activeDirection = F.activeEdgePartialSum u ρ t := by sorry
