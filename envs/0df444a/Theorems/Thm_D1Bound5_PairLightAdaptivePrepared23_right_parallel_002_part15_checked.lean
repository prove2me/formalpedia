-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:04.93256+00:00
-- url     : https://prove2.me/theorems/607246e9-235d-46d6-bfb0-2ba218238027
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 15
-- statement:
--   For prepared pair 23, right list, part 15, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 394 through 405, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part15.lean, lines 10-14, SHA-256 4e062807c2c3c0480c0454027ee01061cb5c49b90398968dde8fc01a7dfdec50. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 394) (PairLightPrepared23.rightRows.drop 394) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
