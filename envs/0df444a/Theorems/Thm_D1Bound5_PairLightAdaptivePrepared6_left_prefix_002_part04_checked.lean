-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:59.784399+00:00
-- url     : https://prove2.me/theorems/3c9d1c56-ddbe-4171-97e9-7d24a96d09cf
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 4
-- statement:
--   For prepared pair 6, left list, part 4, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 188 through 201, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_002Part04.lean, lines 11-16, SHA-256 aa1b76e983b0093910d82a36157be4684267e46ee42419cb7d090edd8e20866d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 14
      (PairLightPrepared6.leftCached.drop 188)
      (PairLightPrepared6.leftRows.drop 188) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
