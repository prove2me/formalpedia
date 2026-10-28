-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part20_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:35.98934+00:00
-- url     : https://prove2.me/theorems/08f130a2-fbf8-412a-80fb-e1e22b6078c8
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 20
-- statement:
--   For prepared pair 15, right list, part 20, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 454 through 465, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part20.lean, lines 10-14, SHA-256 7b7ce4f47daeab50def852961f830a94af0a418353e63186e75ca328530c1405. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part20_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 454) (PairLightPrepared15.rightRows.drop 454) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
