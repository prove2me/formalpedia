-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:40.838308+00:00
-- url     : https://prove2.me/theorems/e1d81a9a-d587-4213-9ec3-cf2865345598
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 14
-- statement:
--   For prepared pair 30, left list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 380 through 391, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part14.lean, lines 10-14, SHA-256 36facbfc581c00e5ac823ebc1f1857b64d1f008edcfd2dedaea857b7da727d1c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 380) (PairLightPrepared30.leftRows.drop 380) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
