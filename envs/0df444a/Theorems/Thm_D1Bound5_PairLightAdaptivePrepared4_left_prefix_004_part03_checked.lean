-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:09.020983+00:00
-- url     : https://prove2.me/theorems/91a1dc50-cf7b-43f1-9d43-3bd91fb0eed5
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 3
-- statement:
--   For prepared pair 4, left list, part 3, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 550 through 595, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_004Part03.lean, lines 11-16, SHA-256 8576214dc42db0da6634611addf936baba1dda5551c72f25a08c7c0c127d7965. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 46
      (PairLightPrepared4.leftCached.drop 550)
      (PairLightPrepared4.leftRows.drop 550) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
