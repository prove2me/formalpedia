-- Prove2me | Theorems.Thm_BKAR_Forest_differentialIdentityAt_emptyParam
-- name    : BKAR.Forest.differentialIdentityAt_emptyParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:25:18.767549+00:00
-- url     : https://prove2.me/theorems/33dd042a-612d-47b8-8b83-e665486a867a
-- title:
--   Forest: differential Identity At empty Param
-- statement:
--   The Forest construction uses the differential Identity At empty Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L319-L325
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L319-L325

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.differentialIdentityAt_emptyParam
    {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (constantConfig t)) :
    deriv (fun s : ℝ => ρ (constantConfig s)) t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) := by sorry
