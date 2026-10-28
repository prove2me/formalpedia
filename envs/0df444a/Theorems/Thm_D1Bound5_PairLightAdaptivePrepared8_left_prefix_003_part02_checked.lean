-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:16.128359+00:00
-- url     : https://prove2.me/theorems/65e8f6e0-3e41-4a03-85ca-e35b5322425a
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 2
-- statement:
--   For prepared pair 8, left list, part 2, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 218 through 231, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_003Part02.lean, lines 11-16, SHA-256 51ba77d89024f6e9059dffbdb70bf238dccc537993f1062bfe206547382b9d04. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.leftCached.drop 218)
      (PairLightPrepared8.leftRows.drop 218) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
