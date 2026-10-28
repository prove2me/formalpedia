-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:39.104486+00:00
-- url     : https://prove2.me/theorems/655a0d08-3a49-4347-aa60-78a8e4b27871
-- title:
--   Selected-floor prefix certificate for prepared pair 18, left list, part 2
-- statement:
--   For prepared pair 18, left list, part 2, the selected-floor certificate succeeds for at most `54` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Original heads 77 through 130; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft18_000Part02.lean, lines 7-11, SHA-256 27e1065c4813e0f1bfc147c72ee9dd22a4d2895e863151ac2294769716320988. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 54
      (leftCached000.drop 77) (leftRows000.drop 77) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
