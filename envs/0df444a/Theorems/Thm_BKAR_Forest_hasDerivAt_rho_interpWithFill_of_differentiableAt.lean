-- Prove2me | Theorems.Thm_BKAR_Forest_hasDerivAt_rho_interpWithFill_of_differentiableAt
-- name    : BKAR.Forest.hasDerivAt_rho_interpWithFill_of_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:15.922644+00:00
-- url     : https://prove2.me/theorems/f840b1b0-1122-4676-8e20-06b484ce989f
-- title:
--   Forest: has Deriv At rho interp With Fill of differentiable At
-- statement:
--   The Forest construction uses the has Deriv At rho interp With Fill of differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L271-L276
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L271-L276

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.hasDerivAt_rho_interpWithFill_of_differentiableAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (F.interpWithFill u t)) :
    HasDerivAt (fun s : ℝ => ρ (F.interpWithFill u s))
      (F.activeEdgePartialSum u ρ t) t := by sorry
