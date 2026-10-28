-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:49.00164+00:00
-- url     : https://prove2.me/theorems/5be59794-cb48-4718-b1a3-a51d95ad187c
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 0
-- statement:
--   For prepared pair 23, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 214 through 225, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part00.lean, lines 10-14, SHA-256 d806afcb2e296331aeecd7acabcc2bb0dbdbf2d646c64dc4888ac2ad9cfbb195. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 214) (PairLightPrepared23.rightRows.drop 214) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
