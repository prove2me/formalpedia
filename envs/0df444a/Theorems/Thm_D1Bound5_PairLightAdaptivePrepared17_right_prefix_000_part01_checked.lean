-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:37.419366+00:00
-- url     : https://prove2.me/theorems/ed99d6cf-d8ad-4a6f-ad51-88b6791f109f
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 1
-- statement:
--   For prepared pair 17, right list, part 1, the selected-floor certificate succeeds for at most `32` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 29 through 60; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_000Part01.lean, lines 7-11, SHA-256 3d6ba61057164c76ecb201a30001bb85b33a46fa50baba40e1e2e6b9463e3b36. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 32
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
