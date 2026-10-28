-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:14.803018+00:00
-- url     : https://prove2.me/theorems/a78c70c4-dd08-443b-8c1a-dd186f36243d
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list, part 1
-- statement:
--   For prepared pair 25, left list, part 1, the selected-floor certificate succeeds for at most `26` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 24 through 49, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_000Part01.lean, lines 7-11, SHA-256 ec21818c5740bac0c66a0d8d3d5c2247f4e42ce5a263c8562265e5265fd08ab5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 26
      (leftCached000.drop 24) (leftRows000.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
