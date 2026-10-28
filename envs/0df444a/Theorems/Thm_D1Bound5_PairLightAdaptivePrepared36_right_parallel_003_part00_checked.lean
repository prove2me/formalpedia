-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:48.284354+00:00
-- url     : https://prove2.me/theorems/0233aeee-0e69-40b1-92c3-4b00ae75c921
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 0
-- statement:
--   For prepared pair 36, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 287 through 298, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part00.lean, lines 10-14, SHA-256 ec42e10c1ac6bea4490efae8962a502a5dafe295f32dcf2a46a79628f69dd9f9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 287) (PairLightPrepared36.rightRows.drop 287) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
