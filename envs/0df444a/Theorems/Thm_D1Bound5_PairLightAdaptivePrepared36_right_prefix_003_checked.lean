-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:06.336461+00:00
-- url     : https://prove2.me/theorems/64021c99-246c-4669-950e-14d6ac666d6d
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list
-- statement:
--   For prepared pair 36, right list, the selected-floor certificate succeeds for at most `273` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight36_003.lean, lines 31-168, SHA-256 525993c75d45bcc7d4428afbd6c653f0e1791c40a5a760db20180ef0a0537e18. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 273
      rightCached003 rightRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
