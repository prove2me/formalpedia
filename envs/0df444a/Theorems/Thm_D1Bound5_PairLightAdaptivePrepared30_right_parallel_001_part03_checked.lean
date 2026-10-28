-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:52.10698+00:00
-- url     : https://prove2.me/theorems/e16c199e-7171-4988-b9a3-f290a6da6129
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 3
-- statement:
--   For prepared pair 30, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 128 through 139, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_001Part03.lean, lines 10-14, SHA-256 f33da1021b74ab9fef0fd7013fba1c132de94ab31935a88495315c81090443c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 128) (PairLightPrepared30.rightRows.drop 128) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
