-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:55.238899+00:00
-- url     : https://prove2.me/theorems/3c75e556-0ac5-46c5-8464-2e42df8c6f2e
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list, part 3
-- statement:
--   For prepared pair 17, right list, part 3, the selected-floor certificate succeeds for at most `41` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 96 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_000Part03.lean, lines 7-11, SHA-256 333cb19547f2ff7cbbe55673e12a70ca10434824b9052ffb3a58d60369feebe1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
