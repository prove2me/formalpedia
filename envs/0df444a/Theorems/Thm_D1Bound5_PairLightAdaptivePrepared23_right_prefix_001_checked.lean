-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:06.113797+00:00
-- url     : https://prove2.me/theorems/77f836b5-bc20-4877-8139-2bc40b4aff0c
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list
-- statement:
--   For prepared pair 23, right list, the selected-floor certificate succeeds for at most `122` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight23_001.lean, lines 19-84, SHA-256 0bc03fa0c5a65d96bb900d327d217b9276606d2ddd0e72eb17d31f598fcce120. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 122
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
