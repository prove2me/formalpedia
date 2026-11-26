-- Prove2me | Theorems.Thm_BKAR_Forest_hasDerivAt_interpWithFill
-- name    : BKAR.Forest.hasDerivAt_interpWithFill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:21.519879+00:00
-- url     : https://prove2.me/theorems/83fd0ccc-d268-42bb-a61a-4862c21c8815
-- title:
--   Forest: has Deriv At interp With Fill
-- statement:
--   The Forest construction uses the has Deriv At interp With Fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L199-L209
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L199-L209

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.hasDerivAt_interpWithFill (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s)
      F.activeDirection t := by sorry
