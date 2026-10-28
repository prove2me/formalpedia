-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:39.084928+00:00
-- url     : https://prove2.me/theorems/8378014a-a52b-44c6-b968-44d95c48b30a
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 2
-- statement:
--   For prepared pair 4, right list, part 2, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 97 through 110, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_001Part02.lean, lines 11-16, SHA-256 d226b882018e43eee08fff5c54da301308df8c94e9c9f1dfb9ee2ff44650df02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.rightCached.drop 97)
      (PairLightPrepared4.rightRows.drop 97) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
