-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:53.295756+00:00
-- url     : https://prove2.me/theorems/b22f6bfb-1884-4ee1-a879-b453e519d959
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list, part 0
-- statement:
--   For prepared pair 25, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 0 through 23, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_000Part00.lean, lines 7-11, SHA-256 1615e5e4a6e3e7a0e8a167bab17555eb6e506d092efde67de2e91554ff247102. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 24
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
