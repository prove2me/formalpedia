-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:36.858992+00:00
-- url     : https://prove2.me/theorems/ca69a672-4d9b-4a09-a144-4eb9fa95e411
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 5
-- statement:
--   For prepared pair 10, left list, part 5, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 58 through 70, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_000Part05.lean, lines 11-16, SHA-256 7c5701e25340c54e565cd525c11d92786552d17ac69ad7d81f37ffd334183724. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.leftCached.drop 58)
      (PairLightPrepared10.leftRows.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
