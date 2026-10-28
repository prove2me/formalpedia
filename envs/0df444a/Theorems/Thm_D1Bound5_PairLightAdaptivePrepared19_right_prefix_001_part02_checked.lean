-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:09.929458+00:00
-- url     : https://prove2.me/theorems/051dd1fe-d72c-41d5-81c6-59b607099d20
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 2
-- statement:
--   For prepared pair 19, right list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 149 through 172, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_001Part02.lean, lines 11-16, SHA-256 2d0b05b8e772bb266b0e720359e7bef31777ae5ad4cb1a21de3593d22dc8376d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 149)
      (PairLightPrepared19.rightRows.drop 149) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
