-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:49.015536+00:00
-- url     : https://prove2.me/theorems/f8e0021d-ce22-4932-8b89-428c0e878993
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 2
-- statement:
--   For prepared pair 1, left list, part 2, the selected-floor certificate succeeds for at most `22` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 36 through 57, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_000Part02.lean, lines 7-11, SHA-256 2e736e00bacab842f4522f583c93d5707a709b98e8259f339615a2b393566c1f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 22
      (leftCached000.drop 36) (leftRows000.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
