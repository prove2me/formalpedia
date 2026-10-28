-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:23.659163+00:00
-- url     : https://prove2.me/theorems/0b214d14-3455-4a9e-a416-6b8b62cecceb
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 8
-- statement:
--   For prepared pair 24, left list, part 8, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 440 through 445, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_002Part08.lean, lines 11-16, SHA-256 107337ba785a99ab3674a8ad96b9045a127ebe32cc15965a076a9feadcb4e880. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 6
      (PairLightPrepared24.leftCached.drop 440)
      (PairLightPrepared24.leftRows.drop 440) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
