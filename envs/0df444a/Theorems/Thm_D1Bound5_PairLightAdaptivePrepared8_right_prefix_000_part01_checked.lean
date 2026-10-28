-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:59.169753+00:00
-- url     : https://prove2.me/theorems/23b7f3c1-2e60-40fa-ba3d-594541272fac
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 1
-- statement:
--   For prepared pair 8, right list, part 1, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 9 through 17, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_000Part01.lean, lines 11-16, SHA-256 433668e2d8f1dd6c2d17780ef1b8720bec47e38b8d12b4165213720a0494de52. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 9
      (PairLightPrepared8.rightCached.drop 9)
      (PairLightPrepared8.rightRows.drop 9) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
