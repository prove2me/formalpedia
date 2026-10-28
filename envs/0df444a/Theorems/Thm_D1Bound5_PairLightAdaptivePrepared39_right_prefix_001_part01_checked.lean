-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:25.651074+00:00
-- url     : https://prove2.me/theorems/2051d478-7498-47ef-9666-6a73d1be602e
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 1
-- statement:
--   For prepared pair 39, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 122 through 145, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_001Part01.lean, lines 11-16, SHA-256 ee1aba5910ec23c5a2ee8a263f5fd2381c6cd980a72d8f0dba1bdde3fb28f041. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 122)
      (PairLightPrepared39.rightRows.drop 122) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
