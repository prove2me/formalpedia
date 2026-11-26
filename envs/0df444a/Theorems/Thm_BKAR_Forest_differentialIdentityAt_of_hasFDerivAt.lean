-- Prove2me | Theorems.Thm_BKAR_Forest_differentialIdentityAt_of_hasFDerivAt
-- name    : BKAR.Forest.differentialIdentityAt_of_hasFDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:53.483869+00:00
-- url     : https://prove2.me/theorems/d22db391-0a4d-5b42-8130-3e336536fe90
-- title:
--   Forest: differential Identity At of has FDeriv At
-- statement:
--   The Forest construction uses the differential Identity At of has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L278-L289
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L278-L289

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.differentialIdentityAt_of_hasFDerivAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    F.ActiveEdgeDerivIdentityAt u ρ t := by sorry
