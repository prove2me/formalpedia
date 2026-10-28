-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:38.646676+00:00
-- url     : https://prove2.me/theorems/54306756-9bdc-41e9-a43a-80386b7fb945
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 0
-- statement:
--   For prepared pair 23, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_000Part00.lean, lines 10-14, SHA-256 3600caa770827f5686fc61a85d371c2f77532daeebd4992ec998e58daad15236. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 0) (PairLightPrepared23.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
