-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:34.999003+00:00
-- url     : https://prove2.me/theorems/dd153c53-4b62-4216-9488-f37f8b0ee048
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 4
-- statement:
--   For prepared pair 1, left list, part 4, the selected-floor certificate succeeds for at most `26` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 82 through 107, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_000Part04.lean, lines 7-11, SHA-256 7ec739479177d16e228c15eccb4270d3cb29a5a7c73aebde5675df5408f8cb9c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 26
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
