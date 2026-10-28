-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:07.259732+00:00
-- url     : https://prove2.me/theorems/e7a162b7-6354-4904-bc97-696d340daa44
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 1
-- statement:
--   For prepared pair 28, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 94 through 105, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_001Part01.lean, lines 10-14, SHA-256 ea469fa4d48507ec6ec09760bd8db9941cf27169b741b0625c1dd26b08f24a39. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 94) (PairLightPrepared28.rightRows.drop 94) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
