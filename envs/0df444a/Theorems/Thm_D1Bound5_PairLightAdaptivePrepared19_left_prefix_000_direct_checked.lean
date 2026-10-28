-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:23.528894+00:00
-- url     : https://prove2.me/theorems/2e5f6a78-8c28-437d-8268-8e43ef8b668a
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list
-- statement:
--   For prepared pair 19, left list, the selected-floor certificate succeeds for at most `101` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft19Prefix000.lean, lines 16-69, SHA-256 58cc0e16c529cc667f5a18903a3a5c481a605f7c36e88feb570a2169af290c62. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 101
      (PairLightPrepared19.leftCached.drop 0) (PairLightPrepared19.leftRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared19
end
