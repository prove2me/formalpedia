-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:52.338143+00:00
-- url     : https://prove2.me/theorems/d4f5bd55-dd14-4c9a-85fb-e233a140a64b
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 5
-- statement:
--   For prepared pair 19, left list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 221 through 244, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_001Part05.lean, lines 11-16, SHA-256 9b8767768ec067c9b953c6b95ecd7b6edc531ad376c5bc67c289089ac67696b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 221)
      (PairLightPrepared19.leftRows.drop 221) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
