-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:15.214073+00:00
-- url     : https://prove2.me/theorems/3fde1cda-65d6-45d6-9880-03246499b839
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 2
-- statement:
--   For prepared pair 15, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 238 through 249, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part02.lean, lines 10-14, SHA-256 5510bb6c482337803dd9dfca864588cc57967dca17926300784c790788ab7f72. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 238) (PairLightPrepared15.rightRows.drop 238) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
