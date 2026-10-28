-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part18_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:55.96046+00:00
-- url     : https://prove2.me/theorems/f4d9b66e-e781-41fd-9f60-e747714e91d8
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 18
-- statement:
--   For prepared pair 30, right list, part 18, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 430 through 441, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part18.lean, lines 10-14, SHA-256 2cd337293f7696976f7e665f913da4cb413ed3501fb8ee9c0afd87a60bc694a7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part18_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 430) (PairLightPrepared30.rightRows.drop 430) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
