-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part17_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:19.419681+00:00
-- url     : https://prove2.me/theorems/94bbb8e7-a774-483c-8476-a6cde7c10bc6
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 17
-- statement:
--   For prepared pair 14, left list, part 17, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 406 through 417, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part17.lean, lines 10-14, SHA-256 9929607f3372332c798f932e3afc92f92aafe32ff7aff6e64871f6948c322ee8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part17_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 406) (PairLightPrepared14.leftRows.drop 406) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
