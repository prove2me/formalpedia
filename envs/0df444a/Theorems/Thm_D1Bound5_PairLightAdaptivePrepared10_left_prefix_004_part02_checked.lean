-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:43.114894+00:00
-- url     : https://prove2.me/theorems/1fef0504-3a60-487b-9ce9-38254052ec8f
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 2
-- statement:
--   For prepared pair 10, left list, part 2, the selected-floor certificate succeeds for at most `64` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 486 through 549, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_004Part02.lean, lines 11-16, SHA-256 6d5d3d42399aa27cd79f26117821429db7e9cd6736f698b4479007a61724c273. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 64
      (PairLightPrepared10.leftCached.drop 486)
      (PairLightPrepared10.leftRows.drop 486) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
