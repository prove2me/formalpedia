-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:16.032999+00:00
-- url     : https://prove2.me/theorems/51a9a320-7ce2-407a-819a-410fa1b38c85
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 4
-- statement:
--   For prepared pair 4, left list, part 4, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 125 through 138, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_001Part04.lean, lines 11-16, SHA-256 4a049b1362236b632e5452f1aa3135320acb1f4e67d21673dacdeea4b9e2320c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.leftCached.drop 125)
      (PairLightPrepared4.leftRows.drop 125) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
