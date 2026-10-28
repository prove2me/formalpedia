-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:33.432829+00:00
-- url     : https://prove2.me/theorems/4ba7a4c7-37e2-42d3-85f9-654e15b4d031
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 4
-- statement:
--   For prepared pair 4, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 46 through 57, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_000Part04.lean, lines 11-16, SHA-256 2b63b96d2cc2c32872e8d927b524b5279eeab9262339495a467ffe66362338e3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 12
      (PairLightPrepared4.leftCached.drop 46)
      (PairLightPrepared4.leftRows.drop 46) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
