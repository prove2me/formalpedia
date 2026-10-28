-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:34.849204+00:00
-- url     : https://prove2.me/theorems/61148f6b-573d-47a3-9065-fd6405f62eb1
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 8
-- statement:
--   For prepared pair 15, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 188 through 199, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part08.lean, lines 10-14, SHA-256 f622d3d48b58017566867b8dabfb81af9e08ce60f5e812b782f0f4f3307d39ec. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 188) (PairLightPrepared15.rightRows.drop 188) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
