-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:30.443836+00:00
-- url     : https://prove2.me/theorems/c7c2f5a5-ec10-49c5-8615-5bcfb0ea9681
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 4
-- statement:
--   For prepared pair 28, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 383 through 394, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part04.lean, lines 10-14, SHA-256 b4ab3aa3b98583a1b7682d5142d5412b17183b0363c1e51c4571adc764b186dc. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 383) (PairLightPrepared28.rightRows.drop 383) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
