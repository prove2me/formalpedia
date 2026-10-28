-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:42.665629+00:00
-- url     : https://prove2.me/theorems/6424d10c-1f5f-4b27-845b-f1b3b731aea7
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list
-- statement:
--   For prepared pair 14, right list, the selected-floor certificate succeeds for at most `88` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight14_000.lean, lines 16-63, SHA-256 71bf70a9c298aca0b5442387bc0cbd8c8475699c6c1a4b31bd86450993ce9437. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 88
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
