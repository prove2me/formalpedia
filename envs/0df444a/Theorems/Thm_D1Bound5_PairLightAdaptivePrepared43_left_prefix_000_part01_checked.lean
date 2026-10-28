-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:32.976133+00:00
-- url     : https://prove2.me/theorems/c356ccad-863b-4cb0-92c0-03b59d780249
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 1
-- statement:
--   For prepared pair 43, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 12 through 23, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_000Part01.lean, lines 8-13, SHA-256 128cdf33847e261edc14f7badeb4f200de7572fea828214e9f973c57fc38e96e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 12)
      (PairLightPrepared43.leftRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
