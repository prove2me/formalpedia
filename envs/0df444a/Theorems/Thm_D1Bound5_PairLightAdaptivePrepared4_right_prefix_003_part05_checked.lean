-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:34.483864+00:00
-- url     : https://prove2.me/theorems/443a0165-0bc1-4456-a86d-8025880f9e9e
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 5
-- statement:
--   For prepared pair 4, right list, part 5, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 371 through 401, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_003Part05.lean, lines 11-16, SHA-256 1854ff28ef99753749da9d4ff7bda0c2837873d41406edcea5048eabd343098d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 31
      (PairLightPrepared4.rightCached.drop 371)
      (PairLightPrepared4.rightRows.drop 371) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
