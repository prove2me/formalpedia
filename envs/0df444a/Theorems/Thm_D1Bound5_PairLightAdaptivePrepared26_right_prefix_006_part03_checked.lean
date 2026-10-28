-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:56.46817+00:00
-- url     : https://prove2.me/theorems/3e7997f9-0658-4d83-9098-ca5b8a573c59
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 3
-- statement:
--   For prepared pair 26, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 479 through 490; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_006Part03.lean, lines 7-11, SHA-256 8e84e5059fa33d3849d462b2248bc2c798cfce337c57f4519e9d4550c0d78b45. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached006.drop 36) (rightRows006.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
