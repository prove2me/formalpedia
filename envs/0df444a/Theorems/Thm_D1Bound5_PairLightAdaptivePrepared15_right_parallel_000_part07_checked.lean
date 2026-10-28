-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:08.754259+00:00
-- url     : https://prove2.me/theorems/612b234f-3c0b-4784-b2b8-cb5815022d91
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 7
-- statement:
--   For prepared pair 15, right list, part 7, the selected-floor certificate succeeds for at most `8` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 84 through 91, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_000Part07.lean, lines 10-14, SHA-256 48c29b95dcd8f28e8fda168bd65877caf0425c016a6a13b46dc589952971cb3a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part07_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 8
      (PairLightPrepared15.rightCached.drop 84) (PairLightPrepared15.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
