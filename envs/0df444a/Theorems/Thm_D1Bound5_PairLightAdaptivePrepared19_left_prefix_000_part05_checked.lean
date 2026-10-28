-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:54.887201+00:00
-- url     : https://prove2.me/theorems/ed227d42-9fbd-4633-9d41-a68674f3a4d1
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 5
-- statement:
--   For prepared pair 19, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 60 through 71, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_000Part05.lean, lines 11-16, SHA-256 f4836273c733d444e9e1e77dc149d793bddfcde0e1b9583444d4cbd10cfa93b8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.leftCached.drop 60)
      (PairLightPrepared19.leftRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
