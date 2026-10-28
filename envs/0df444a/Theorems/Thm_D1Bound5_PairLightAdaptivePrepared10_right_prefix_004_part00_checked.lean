-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_004_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:07.429741+00:00
-- url     : https://prove2.me/theorems/dd63f644-e1c8-4e67-ba10-cb8afe6c7140
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 0
-- statement:
--   For prepared pair 10, right list, part 0, the selected-floor certificate succeeds for at most `36` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 405 through 440, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_004Part00.lean, lines 11-16, SHA-256 29880a071b54584346f20e35b6d03e51600b79edcfaf7adcf7b4f4fea6797787. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 36
      (PairLightPrepared10.rightCached.drop 405)
      (PairLightPrepared10.rightRows.drop 405) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
