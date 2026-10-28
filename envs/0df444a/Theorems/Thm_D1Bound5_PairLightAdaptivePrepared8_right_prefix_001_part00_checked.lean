-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:30.8934+00:00
-- url     : https://prove2.me/theorems/56506281-5ec3-4d54-a2fa-9e2c3fdb1f81
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 0
-- statement:
--   For prepared pair 8, right list, part 0, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 58 through 67, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_001Part00.lean, lines 11-16, SHA-256 7257dc5dcc6cc0bcaece2fe90cc2f68ea2ae461a5cb4882eb959efed4ee30d74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.rightCached.drop 58)
      (PairLightPrepared8.rightRows.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
