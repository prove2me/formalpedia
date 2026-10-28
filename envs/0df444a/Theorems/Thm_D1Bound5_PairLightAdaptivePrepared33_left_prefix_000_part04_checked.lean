-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:04.949298+00:00
-- url     : https://prove2.me/theorems/7237e49c-8426-4fbd-93d2-c249ef735da3
-- title:
--   Selected-floor prefix certificate for prepared pair 33, left list, part 4
-- statement:
--   For prepared pair 33, left list, part 4, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared33.sieve`. Original heads 134 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft33_000Part04.lean, lines 7-11, SHA-256 24d94d51fd321ef97721e414200518dce96f0d1e74d5b3371d5a9c2dd6bbea01. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared33
end
