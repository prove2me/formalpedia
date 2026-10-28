-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:37.111259+00:00
-- url     : https://prove2.me/theorems/31247f22-f49d-4ee2-8151-8893427ad678
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 2
-- statement:
--   For prepared pair 17, right list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 61 through 95; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_000Part02.lean, lines 7-11, SHA-256 1c837fb4b8965b42108680425b5acd8f49a760d983cc11af7d771d7aa860ee23. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 35
      (rightCached000.drop 61) (rightRows000.drop 61) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
