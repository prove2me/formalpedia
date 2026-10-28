-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:52.136513+00:00
-- url     : https://prove2.me/theorems/423a450f-0697-42af-aa71-c2d5c2a6da60
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 0
-- statement:
--   For prepared pair 1, left list, part 0, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 137 through 170, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_001Part00.lean, lines 7-11, SHA-256 cae40fe8c0ed95536f6c1a6ea057e2a8bdf6a5988c09252ee7f9fb7ec80bbe44. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 34
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
