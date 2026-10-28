-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:19.838608+00:00
-- url     : https://prove2.me/theorems/23103063-e115-4cf8-a21f-0b92ae9221a6
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list
-- statement:
--   For prepared pair 19, right list, the selected-floor certificate succeeds for at most `198` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight19Prefix002.lean, lines 16-69, SHA-256 41e852e15af8f2d0abf2747960a535f8eaa3bb87ced35890c29abf872ea82b91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 198
      (PairLightPrepared19.rightCached.drop 248) (PairLightPrepared19.rightRows.drop 248) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared19
end
