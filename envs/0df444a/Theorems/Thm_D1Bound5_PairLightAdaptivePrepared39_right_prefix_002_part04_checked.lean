-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:58.602979+00:00
-- url     : https://prove2.me/theorems/5000d19a-6c16-4e08-841e-e80fcf302593
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 4
-- statement:
--   For prepared pair 39, right list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 332 through 355, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_002Part04.lean, lines 11-16, SHA-256 6928a7b8c510db5e17672772b50c83a276b5cc9ce3fbbed821b61a6a8aec9b10. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 332)
      (PairLightPrepared39.rightRows.drop 332) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
