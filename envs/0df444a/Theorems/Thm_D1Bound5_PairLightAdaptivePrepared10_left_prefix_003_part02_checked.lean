-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:29.722262+00:00
-- url     : https://prove2.me/theorems/5dc3ea54-a472-4314-a1d0-66dea5733be0
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 2
-- statement:
--   For prepared pair 10, left list, part 2, the selected-floor certificate succeeds for at most `23` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 296 through 318, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_003Part02.lean, lines 11-16, SHA-256 050d78a16a929a97b0d91398cbb7c3a36dba143288a86435b2e191f720ad3846. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 23
      (PairLightPrepared10.leftCached.drop 296)
      (PairLightPrepared10.leftRows.drop 296) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
