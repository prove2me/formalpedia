-- Prove2me | Theorems.Thm_Csg_rpsHi_prefixed
-- name    : Csg.rpsHi_prefixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:11:42.995306+00:00
-- url     : https://prove2.me/theorems/c227d819-f53b-4ce1-8321-8618fd11f0ec
-- title:
--   Csg: rps Hi prefixed
-- statement:
--   **The payoff, upper half, and the interval-specific content.** `rpsHi` is a pre-fixed point of
--       `reachOp` -- `win1`/`win2` close by the same `change`/`rw` idiom every worked instance uses,
--       landing on a trivial `x ≤ x` rather than `RockPaperScissorsLfp.lean`'s `x = x`; `draw` is tight
--       (`reachOp rpsHi draw = rpsHi initial = rpsHi draw` exactly); `initial` is the one genuinely
--       slack inequality, `5/9 ≤ 2/3`, checked directly by `norm_num` rather than forced by any
--       symmetry argument.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L119-L136
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L119-L136

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
set_option autoImplicit true
open Csg

theorem Csg.rpsHi_prefixed : rpsCSG.reachOp rpsGoalWin2 rpsR_zero rpsHi ≤ rpsHi := by sorry
