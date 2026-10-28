-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:02.50632+00:00
-- url     : https://prove2.me/theorems/9d1ca51e-c4d9-4683-a5b4-e20d4dfaa4ce
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 2
-- statement:
--   For prepared pair 8, left list, part 2, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 18 through 27, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_000Part02.lean, lines 11-16, SHA-256 321865135b7620cd86e4b3358e5bf6e7c2bb24abf926a413c1137928667630d5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.leftCached.drop 18)
      (PairLightPrepared8.leftRows.drop 18) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
