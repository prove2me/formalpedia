-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:17.511606+00:00
-- url     : https://prove2.me/theorems/5c89b31e-9e04-490f-acc4-464acbaeb3f9
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 4
-- statement:
--   For prepared pair 24, right list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 197 through 220, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_001Part04.lean, lines 11-16, SHA-256 addbbf6b22b21557e8d19950d6779fe3e5bedc816112075c32033fd174c02cef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 197)
      (PairLightPrepared24.rightRows.drop 197) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
