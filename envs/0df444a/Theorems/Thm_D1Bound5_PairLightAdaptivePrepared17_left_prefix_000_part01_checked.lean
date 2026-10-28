-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:54.091351+00:00
-- url     : https://prove2.me/theorems/a0355cbb-4f90-445f-a8b5-1fc311f5e683
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 1
-- statement:
--   For prepared pair 17, left list, part 1, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 28 through 58; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_000Part01.lean, lines 7-11, SHA-256 d92748f95d987c240cc94949aa6ad0fbfc04f40073655c8cbbed0801d1591a1c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 31
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
