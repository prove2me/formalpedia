-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:27.259442+00:00
-- url     : https://prove2.me/theorems/5cfbe93c-ce93-4214-96b9-c4f355a499c7
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 8
-- statement:
--   For prepared pair 19, left list, part 8, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 440 through 445, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_002Part08.lean, lines 11-16, SHA-256 be794e4d1c9cb4d6cec4d97a5e2b2cc67754a873e6722e401617a18ede58f53c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 6
      (PairLightPrepared19.leftCached.drop 440)
      (PairLightPrepared19.leftRows.drop 440) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
