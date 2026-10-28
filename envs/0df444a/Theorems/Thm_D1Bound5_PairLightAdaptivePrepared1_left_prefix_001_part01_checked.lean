-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:34.773607+00:00
-- url     : https://prove2.me/theorems/9fb62ebe-e657-4a96-83f2-9743a8385bbe
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 1
-- statement:
--   For prepared pair 1, left list, part 1, the selected-floor certificate succeeds for at most `42` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 171 through 212, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_001Part01.lean, lines 7-11, SHA-256 0ed78a5921718702beae5d92eca1e444cded2c750838569dc9fe3df2ee25977d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 42
      (leftCached001.drop 34) (leftRows001.drop 34) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
