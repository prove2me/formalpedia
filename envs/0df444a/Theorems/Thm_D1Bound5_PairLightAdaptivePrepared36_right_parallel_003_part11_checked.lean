-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:35.602505+00:00
-- url     : https://prove2.me/theorems/5232e093-d1c6-42bb-812e-d9572c7191ec
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 11
-- statement:
--   For prepared pair 36, right list, part 11, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 419 through 430, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part11.lean, lines 10-14, SHA-256 d198cea79d81a177320283f4dac66d897d3c8cb187f5d5fe1a30337616d4d4d3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part11_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 419) (PairLightPrepared36.rightRows.drop 419) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
