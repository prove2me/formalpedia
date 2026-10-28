-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:11.69241+00:00
-- url     : https://prove2.me/theorems/05b5a0b3-bde3-408f-8e69-8c30b2ebdb00
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 2
-- statement:
--   For prepared pair 10, left list, part 2, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 97 through 110, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_001Part02.lean, lines 11-16, SHA-256 e5c73f3a8224065460e84a724b5bebe3929cdc0135aae0009f574bbf075b1cca. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 14
      (PairLightPrepared10.leftCached.drop 97)
      (PairLightPrepared10.leftRows.drop 97) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
