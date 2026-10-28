-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:53.521762+00:00
-- url     : https://prove2.me/theorems/747cf6b4-00b4-40fc-b6d1-49edc4d2fa7e
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 4
-- statement:
--   For prepared pair 39, right list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 194 through 217, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_001Part04.lean, lines 11-16, SHA-256 91e12ca44d9f067eb2f79db9deb4515b006a93081fad6229f29e37ea90736a23. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 194)
      (PairLightPrepared39.rightRows.drop 194) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
