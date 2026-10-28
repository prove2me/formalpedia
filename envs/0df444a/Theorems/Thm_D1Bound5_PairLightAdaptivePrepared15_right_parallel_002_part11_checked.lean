-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:37.995665+00:00
-- url     : https://prove2.me/theorems/cf383a24-91a8-47e4-b89a-c0a2e4a136e4
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 11
-- statement:
--   For prepared pair 15, right list, part 11, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 346 through 357, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part11.lean, lines 10-14, SHA-256 50ede319a9c410a573338916b294670ff2bff46407d3fc58c6dcf9263cc2c31f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part11_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 346) (PairLightPrepared15.rightRows.drop 346) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
