-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:51.994158+00:00
-- url     : https://prove2.me/theorems/3d5ed658-8979-4fa5-afb9-d6b023d50f62
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list
-- statement:
--   For prepared pair 14, left list, the selected-floor certificate succeeds for at most `76` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft14_003.lean, lines 15-56, SHA-256 c076ecf3a36f7974d34efe8f0165c82fa24942e0262492778c32f4ea4cd5c2df. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 76
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
