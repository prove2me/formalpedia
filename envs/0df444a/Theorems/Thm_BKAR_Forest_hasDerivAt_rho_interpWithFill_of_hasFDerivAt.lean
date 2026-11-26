-- Prove2me | Theorems.Thm_BKAR_Forest_hasDerivAt_rho_interpWithFill_of_hasFDerivAt
-- name    : BKAR.Forest.hasDerivAt_rho_interpWithFill_of_hasFDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:50.062806+00:00
-- url     : https://prove2.me/theorems/ed593650-4fc3-5f1b-afc5-5abab9bcd536
-- title:
--   Forest: has Deriv At rho interp With Fill of has FDeriv At
-- statement:
--   The Forest construction uses the has Deriv At rho interp With Fill of has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L260-L269
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L260-L269

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.hasDerivAt_rho_interpWithFill_of_hasFDerivAt (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    HasDerivAt (fun s : ℝ => ρ (F.interpWithFill u s))
      (F.activeEdgePartialSum u ρ t) t := by sorry
