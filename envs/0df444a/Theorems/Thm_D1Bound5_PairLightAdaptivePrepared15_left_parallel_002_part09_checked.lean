-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:10.647337+00:00
-- url     : https://prove2.me/theorems/05cf2dbf-f1bc-4565-bc0d-f149a903953a
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 9
-- statement:
--   For prepared pair 15, left list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 322 through 333, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part09.lean, lines 10-14, SHA-256 f90113a9e1cc82dded5c3fdd3b38fbee3ab2f1be6590e82598a5feb63ee00f3b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part09_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 322) (PairLightPrepared15.leftRows.drop 322) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
