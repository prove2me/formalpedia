-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:05.128443+00:00
-- url     : https://prove2.me/theorems/2f963408-0ea8-43a7-840f-1431676ce2b3
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 1
-- statement:
--   For prepared pair 14, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 12 through 23, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_000Part01.lean, lines 10-14, SHA-256 31ffc38ac470e3365ddf89a3aed9173aa39b55ca82c95d1d48c6afa44a21d1a6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 12) (PairLightPrepared14.rightRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
