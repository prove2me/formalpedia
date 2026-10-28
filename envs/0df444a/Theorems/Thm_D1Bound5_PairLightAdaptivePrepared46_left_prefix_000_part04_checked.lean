-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:11.636305+00:00
-- url     : https://prove2.me/theorems/88b20685-dd7c-404b-8e3c-9e08ffbec2ea
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 4
-- statement:
--   For prepared pair 46, left list, part 4, the selected-floor certificate succeeds for at most `26` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 82 through 107, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000Part04.lean, lines 7-11, SHA-256 abfcb0567959f973ba953eeb54484a8a85f5b681cf355ba438ff90b1f13cc87f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 26
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
