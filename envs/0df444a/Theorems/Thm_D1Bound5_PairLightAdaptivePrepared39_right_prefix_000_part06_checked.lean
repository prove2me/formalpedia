-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:02.215994+00:00
-- url     : https://prove2.me/theorems/ec5d146e-a584-4b2f-852c-315d3869248a
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 6
-- statement:
--   For prepared pair 39, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 72 through 83, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_000Part06.lean, lines 11-16, SHA-256 592b569ef629489c916fdd2e0c076c2684dff27df68a23d3fd81fa840bf59c58. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.rightCached.drop 72)
      (PairLightPrepared39.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
