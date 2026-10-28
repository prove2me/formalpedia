-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:46.434205+00:00
-- url     : https://prove2.me/theorems/d7fbe73f-f4fe-4354-bac5-779e9f33ebcd
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 4
-- statement:
--   For prepared pair 23, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 262 through 273, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part04.lean, lines 10-14, SHA-256 196a6d610e4dbba9b93065df133ae99d51f95cc13c551a3eeca285a43dd389ba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 262) (PairLightPrepared23.rightRows.drop 262) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
