-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:47.415463+00:00
-- url     : https://prove2.me/theorems/93ca84c8-c792-4130-834a-38afebc8734f
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 7
-- statement:
--   For prepared pair 3, right list, part 7, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 279 through 302, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_001Part07.lean, lines 10-15, SHA-256 5d488b41b4b0f6d7d55fb3e80e0c2e53cc7a6b0d3a440612ecc2418ccf43e16e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part07_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.rightCached.drop 279)
      (PairLightPrepared3.rightRows.drop 279) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
