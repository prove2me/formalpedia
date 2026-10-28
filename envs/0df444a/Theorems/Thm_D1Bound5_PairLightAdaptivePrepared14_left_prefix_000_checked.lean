-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:12.245435+00:00
-- url     : https://prove2.me/theorems/c3261dda-a196-4722-b699-8bbd2e3e2b24
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list
-- statement:
--   For prepared pair 14, left list, the selected-floor certificate succeeds for at most `88` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft14_000.lean, lines 16-63, SHA-256 6bda8e695240495022736e821070a5c36fe914b901783679bae44b2e33ca3d35. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 88
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
