-- Prove2me | Theorems.Thm_Csg_rpsCSG_safetyOp_gfp_eq
-- name    : Csg.rpsCSG_safetyOp_gfp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:11:41.207656+00:00
-- url     : https://prove2.me/theorems/46597fe6-0366-41c4-8014-0a994bb83ace
-- title:
--   Csg: rps CSG safety Op gfp eq
-- statement:
--   **The headline result.** `rpsVStarSafety` -- the constant `0` function -- *is* the greatest
--       fixed point of `safetyOp rpsSafeUnresolved`, on the nose: the two payoff lemmas above fed into
--       `SafetyCertificate.lean`'s reusable `CSG.safetyOp_gfp_eq_of_certificate` combinator. The first
--       real exercise of that combinator against a concrete instance, not just the fully general
--       statement it specialises.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L144-L147
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L144-L147

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_safetyOp_gfp_eq :
    (rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero).gfp = rpsVStarSafety := by sorry
