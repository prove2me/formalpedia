-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:53.735181+00:00
-- url     : https://prove2.me/theorems/b53a6c49-b9b7-4015-8f3c-40c2b2ddaad4
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 3
-- statement:
--   For prepared pair 8, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 156 through 167, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_002Part03.lean, lines 11-16, SHA-256 0e99958396965142d4e09e8d2ce6af8ab75c7487e6be0ddf7e15b11c6076520d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 156)
      (PairLightPrepared8.leftRows.drop 156) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
