-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part19_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:06.718711+00:00
-- url     : https://prove2.me/theorems/be5f5a11-2c8a-4969-b0e1-795ea16b4997
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 19
-- statement:
--   For prepared pair 30, right list, part 19, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 442 through 453, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part19.lean, lines 10-14, SHA-256 6940f7d77806c4df75c1ea1fb146914c8d3e571179650531dc79fe2ef831c68a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part19_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 442) (PairLightPrepared30.rightRows.drop 442) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
