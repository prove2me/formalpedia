-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:43.615122+00:00
-- url     : https://prove2.me/theorems/32252553-bb49-4010-b575-ac546fd1709f
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 5
-- statement:
--   For prepared pair 4, left list, part 5, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 139 through 152, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_001Part05.lean, lines 11-16, SHA-256 e6fdc1aba73f180773348b4ed989e8a476ca512af2d02db465ce4acb618822eb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.leftCached.drop 139)
      (PairLightPrepared4.leftRows.drop 139) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
