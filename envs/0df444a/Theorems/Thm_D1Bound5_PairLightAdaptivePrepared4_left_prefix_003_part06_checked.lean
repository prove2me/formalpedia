-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:56:45.417621+00:00
-- url     : https://prove2.me/theorems/8dd915c5-8689-477a-9727-c725dd2d4b1d
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 6
-- statement:
--   For prepared pair 4, left list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 402 through 404, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_003Part06.lean, lines 11-16, SHA-256 c1d321d0be46cce79d0cd6bfc66cd59ac6412db9f357fae09fa54666a165075e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 3
      (PairLightPrepared4.leftCached.drop 402)
      (PairLightPrepared4.leftRows.drop 402) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
