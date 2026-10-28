-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:37.008593+00:00
-- url     : https://prove2.me/theorems/406f9b04-6ca6-4d49-bccf-bcb8d7f658c1
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list
-- statement:
--   For prepared pair 36, left list, the selected-floor certificate succeeds for at most `275` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft36_003.lean, lines 31-168, SHA-256 1e7ff3ee0cbafed0865dea3decbaac4d0daac680109ad3e1bfafdaf95382c839. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 275
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
