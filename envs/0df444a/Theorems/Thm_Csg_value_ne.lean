-- Prove2me | Theorems.Thm_Csg_value_ne
-- name    : Csg.value_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:04:44.773238+00:00
-- url     : https://prove2.me/theorems/b97ab754-5d39-4e77-95bf-79d6c92d0cdb
-- title:
--   Csg: value ne
-- statement:
--   **The point of this file.** The two directions disagree: `⟨⟨hider⟩⟩ P_max`-shaped value `1/2`
--       is not `⟨⟨hider⟩⟩ P_min`-shaped value `4/5`, for two stage games that are transposes of each
--       other by construction (see the module docstring) -- a genuine, hand-verified instance of
--       `value(M) ≠ value(Mᵀ)`, unreachable at `2×2` (every such instance in this project collapses,
--       see above) and made possible here by `feint`, the one new action beyond plain SKIRMISH.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L392-L398
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L392-L398

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.value_ne (vMin vMax : SkirmishState → ℝ)
    (vMinHide : vMin .hide = 4 / 5) (vMinHome : vMin .home = 1) (vMinWet : vMin .wet = 0)
    (vMaxHide : vMax .hide = 1 / 2) (vMaxHome : vMax .home = 1) (vMaxWet : vMax .wet = 0) :
    (skirmishMaxCSG.stageGame .hide vMax).value ≠ (skirmishMinCSG.stageGame .hide vMin).value := by sorry
