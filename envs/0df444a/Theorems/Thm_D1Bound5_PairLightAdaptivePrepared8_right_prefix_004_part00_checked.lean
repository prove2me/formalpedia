-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:07.434979+00:00
-- url     : https://prove2.me/theorems/4ff86a59-ba88-4de5-825c-8a9f9dc4bf44
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 0
-- statement:
--   For prepared pair 8, right list, part 0, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 274 through 288, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_004Part00.lean, lines 11-16, SHA-256 6278b816beee115957e43e10845ff27a6d028d148e508b95e1e05bbe50b8781f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 15
      (PairLightPrepared8.rightCached.drop 274)
      (PairLightPrepared8.rightRows.drop 274) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
