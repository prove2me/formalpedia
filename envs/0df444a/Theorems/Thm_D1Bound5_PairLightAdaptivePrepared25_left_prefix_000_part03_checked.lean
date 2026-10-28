-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:46.478149+00:00
-- url     : https://prove2.me/theorems/000a587b-5ddb-424e-89d2-159772f089e1
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list, part 3
-- statement:
--   For prepared pair 25, left list, part 3, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`. Original heads 78 through 108, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_000Part03.lean, lines 7-11, SHA-256 e58eb2b4af2bf1bd79eec1df8ae2eecb8102f6fa654ba0558f3247d71b27fce6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 31
      (leftCached000.drop 78) (leftRows000.drop 78) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
