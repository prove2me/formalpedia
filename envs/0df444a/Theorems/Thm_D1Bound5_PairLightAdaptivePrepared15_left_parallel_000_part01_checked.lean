-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:04.284097+00:00
-- url     : https://prove2.me/theorems/53f0d320-7acb-48f4-9823-8a15e87b7a0a
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 1
-- statement:
--   For prepared pair 15, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 12 through 23, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_000Part01.lean, lines 10-14, SHA-256 2968e319682dab18f6254ed6e516a7ae5d7f04c8d428f1053ca3fc8a40b809a3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 12) (PairLightPrepared15.leftRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
