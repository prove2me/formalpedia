-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:05.600929+00:00
-- url     : https://prove2.me/theorems/8161900b-85eb-48a7-a92a-c21721ecfdae
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 2
-- statement:
--   For prepared pair 14, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 443 through 454, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_003Part02.lean, lines 10-14, SHA-256 7d1933a3c52b554362593a493c1d20412b9c253599a331977c6d1940efb97b99. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 443) (PairLightPrepared14.leftRows.drop 443) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
