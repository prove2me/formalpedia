-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:57.200615+00:00
-- url     : https://prove2.me/theorems/abb5837b-0288-47eb-a49e-440887c70bab
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 4
-- statement:
--   For prepared pair 15, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 48 through 59, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_000Part04.lean, lines 10-14, SHA-256 1c896b7eccf38fcc1fed792c33c81c524848dce87be8f2752206b96c158e0d0e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 48) (PairLightPrepared15.rightRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
