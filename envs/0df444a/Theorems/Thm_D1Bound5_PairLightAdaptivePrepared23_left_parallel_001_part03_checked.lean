-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:58.584012+00:00
-- url     : https://prove2.me/theorems/b14c0f34-952b-4dc6-96d3-0b30dbe0b056
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 3
-- statement:
--   For prepared pair 23, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 127 through 138, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_001Part03.lean, lines 10-14, SHA-256 6040ca687a15c8f8758907a91965afca5172e6c91a97f84e843697a18576f080. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 127) (PairLightPrepared23.leftRows.drop 127) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
