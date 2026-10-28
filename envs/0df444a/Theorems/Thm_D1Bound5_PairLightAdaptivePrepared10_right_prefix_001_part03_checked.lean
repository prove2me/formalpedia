-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:07.459557+00:00
-- url     : https://prove2.me/theorems/fb451588-dc27-4b5c-8923-8378ffa8dc6f
-- title:
--   Selected-floor prefix certificate for prepared pair 10, right list, part 3
-- statement:
--   For prepared pair 10, right list, part 3, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 111 through 124, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight10_001Part03.lean, lines 11-16, SHA-256 34964673f513b77e583ee74e6e2fd34682e597ccac4680201adea11270d3864a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 14
      (PairLightPrepared10.rightCached.drop 111)
      (PairLightPrepared10.rightRows.drop 111) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
