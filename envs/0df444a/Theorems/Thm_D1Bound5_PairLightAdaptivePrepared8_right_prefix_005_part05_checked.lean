-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:04.570873+00:00
-- url     : https://prove2.me/theorems/18828ab3-1a64-466f-8b15-17e18f874fb5
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list, part 5
-- statement:
--   For prepared pair 8, right list, part 5, the selected-floor certificate succeeds for at most `30` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 491 through 520, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_005Part05.lean, lines 11-16, SHA-256 ba3c2bf72df68e1dd7c6da43727924584448934ff8fe9174c283d90df7afc448. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 30
      (PairLightPrepared8.rightCached.drop 491)
      (PairLightPrepared8.rightRows.drop 491) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
