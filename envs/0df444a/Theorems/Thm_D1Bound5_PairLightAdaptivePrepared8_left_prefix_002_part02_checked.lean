-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:52.636135+00:00
-- url     : https://prove2.me/theorems/633c172e-37f2-4197-a755-609a05ab0279
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 2
-- statement:
--   For prepared pair 8, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 144 through 155, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_002Part02.lean, lines 11-16, SHA-256 71dcb19871afd0021774f015b75bf7cf2fc0ad83c2afc89797243abbcaebc32e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 144)
      (PairLightPrepared8.leftRows.drop 144) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
