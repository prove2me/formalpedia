-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:01.772888+00:00
-- url     : https://prove2.me/theorems/b06421da-321a-4473-99b4-0a9ab515fa1c
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 1
-- statement:
--   For prepared pair 6, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 75 through 86, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_001Part01.lean, lines 11-16, SHA-256 7cbda726302c374baefa1a755e14b18d346fc028cc6f17d898a9b4138f7c31b0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.rightCached.drop 75)
      (PairLightPrepared6.rightRows.drop 75) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
