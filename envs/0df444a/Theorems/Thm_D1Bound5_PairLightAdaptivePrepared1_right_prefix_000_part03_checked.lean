-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:51.804475+00:00
-- url     : https://prove2.me/theorems/bb1cc671-f58e-4cc4-bf2b-5572fb1cad43
-- title:
--   Selected-floor prefix certificate for prepared pair 1, right list, part 3
-- statement:
--   For prepared pair 1, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 58 through 81, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight1_000Part03.lean, lines 7-11, SHA-256 a169ffe2ab751b6674c00b3a99452af1a197c8476cf819193847b01733d5104a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 24
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
