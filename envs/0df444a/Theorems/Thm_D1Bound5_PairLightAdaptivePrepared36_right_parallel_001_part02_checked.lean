-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:16.706788+00:00
-- url     : https://prove2.me/theorems/c95df5f4-9ef4-4927-9bf7-8b3f8d2a0271
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 2
-- statement:
--   For prepared pair 36, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 100 through 111, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part02.lean, lines 10-14, SHA-256 681364d438edb44457b141fc8b199490b74ac0da67cd982f1dc4db373e229ff7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 100) (PairLightPrepared36.rightRows.drop 100) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
