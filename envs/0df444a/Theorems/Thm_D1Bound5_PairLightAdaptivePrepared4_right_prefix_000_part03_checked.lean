-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:10.136083+00:00
-- url     : https://prove2.me/theorems/be22cb48-ece4-4a08-8d5a-51e20998e850
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 3
-- statement:
--   For prepared pair 4, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 34 through 45, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_000Part03.lean, lines 11-16, SHA-256 37eb38a26fd3905e1902f561475e3123b5d04247c6be5ce9fb815c80ac178927. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 12
      (PairLightPrepared4.rightCached.drop 34)
      (PairLightPrepared4.rightRows.drop 34) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
