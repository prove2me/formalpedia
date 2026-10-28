-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:19.754901+00:00
-- url     : https://prove2.me/theorems/31813197-760c-4387-aad4-0afc20b69e22
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 4
-- statement:
--   For prepared pair 26, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 491 through 502; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_006Part04.lean, lines 7-11, SHA-256 c265497580ba9de86db0038a1353a231c215d14939ba7edc52a32d482d573b49. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached006.drop 48) (leftRows006.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
