-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:39.67081+00:00
-- url     : https://prove2.me/theorems/b3285ac0-e0ef-420b-abd7-134883327b87
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 10
-- statement:
--   For prepared pair 15, left list, part 10, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 212 through 213, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_001Part10.lean, lines 10-14, SHA-256 9850c5610d8f4037f40236148cde6672bbb2637ddc44926ee94e31f46b620d29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part10_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 2
      (PairLightPrepared15.leftCached.drop 212) (PairLightPrepared15.leftRows.drop 212) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
