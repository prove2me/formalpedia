-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:44.63795+00:00
-- url     : https://prove2.me/theorems/1309641e-1447-4e06-853d-87f7ff42a6ca
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 4
-- statement:
--   For prepared pair 8, left list, part 4, the selected-floor certificate succeeds for at most `18` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 339 through 356, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_004Part04.lean, lines 11-16, SHA-256 7947b61ffab60f4d69085c6e3b2c16ac8b9c9f9f200cb5ad6f2b81f75fbaebc8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 18
      (PairLightPrepared8.leftCached.drop 339)
      (PairLightPrepared8.leftRows.drop 339) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
