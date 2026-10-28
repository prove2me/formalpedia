-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:45.417426+00:00
-- url     : https://prove2.me/theorems/f915f728-4e70-46ee-9a10-12ee0862cbdf
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 15
-- statement:
--   For prepared pair 28, right list, part 15, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 515 through 523, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part15.lean, lines 10-14, SHA-256 e164af07d441bee8c7777ba7c256e7342f1168b7295c9ac7f439ba16115b4c06. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 9
      (PairLightPrepared28.rightCached.drop 515) (PairLightPrepared28.rightRows.drop 515) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
