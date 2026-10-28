-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:07.389955+00:00
-- url     : https://prove2.me/theorems/cd1c8244-4f2a-4d8c-95db-11755eb8d68c
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 5
-- statement:
--   For prepared pair 4, right list, part 5, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 58 through 70, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_000Part05.lean, lines 11-16, SHA-256 53881bab050c5003cfa02da3023d8c1aaaebe6ca52f46d5d956c84bdec004108. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 13
      (PairLightPrepared4.rightCached.drop 58)
      (PairLightPrepared4.rightRows.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
