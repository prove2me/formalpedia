-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:34.578994+00:00
-- url     : https://prove2.me/theorems/2eee21c2-cd80-4fa0-aa6f-7ead4fb3d15d
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 7
-- statement:
--   For prepared pair 14, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 286 through 297, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part07.lean, lines 10-14, SHA-256 41c890a91b3c782dc76152162aca63bec712cc5b3ce38c82e3bed2a7e523688c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part07_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 286) (PairLightPrepared14.leftRows.drop 286) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
