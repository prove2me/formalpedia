-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:26.583986+00:00
-- url     : https://prove2.me/theorems/5f830557-327d-40f3-85f2-c462458ca977
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 5
-- statement:
--   For prepared pair 28, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 244 through 255, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_002Part05.lean, lines 10-14, SHA-256 9a3b1b65442f50fbfc5a2ce7941735b25a85035d1c932b486d3e876de770f728. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 244) (PairLightPrepared28.rightRows.drop 244) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
