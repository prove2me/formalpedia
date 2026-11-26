-- Prove2me | Theorems.Thm_BKAR_Forest_differentialIdentityAt_of_differentiableAt
-- name    : BKAR.Forest.differentialIdentityAt_of_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:04.12466+00:00
-- url     : https://prove2.me/theorems/cfabf9a0-b515-4aa3-93ab-453402055661
-- title:
--   Forest: differential Identity At of differentiable At
-- statement:
--   The Forest construction uses the differential Identity At of differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L291-L295
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L291-L295

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.differentialIdentityAt_of_differentiableAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (F.interpWithFill u t)) :
    F.ActiveEdgeDerivIdentityAt u ρ t := by sorry
