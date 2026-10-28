-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:28.785341+00:00
-- url     : https://prove2.me/theorems/790edc40-6181-43fa-b0e7-e52644cd5028
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 5
-- statement:
--   For prepared pair 4, left list, part 5, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 371 through 401, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_003Part05.lean, lines 11-16, SHA-256 32e5f5badc520826554bbe661cd9481ebeec132a29a00178655979d8d4e5e29a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 31
      (PairLightPrepared4.leftCached.drop 371)
      (PairLightPrepared4.leftRows.drop 371) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
