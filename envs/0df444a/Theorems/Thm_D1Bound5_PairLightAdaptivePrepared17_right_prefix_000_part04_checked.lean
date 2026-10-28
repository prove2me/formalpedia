-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:54.802176+00:00
-- url     : https://prove2.me/theorems/794a951c-4366-4b80-9628-37dc501829c3
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 4
-- statement:
--   For prepared pair 17, right list, part 4, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 137 through 137; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_000Part04.lean, lines 7-11, SHA-256 219b0ad984f21ae0611b81852383fbf0039d7ce7e8ee425fb092822509d560c4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 1
      (rightCached000.drop 137) (rightRows000.drop 137) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
