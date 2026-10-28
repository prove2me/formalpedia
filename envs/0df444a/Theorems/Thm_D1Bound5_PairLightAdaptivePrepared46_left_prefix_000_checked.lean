-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:34.9061+00:00
-- url     : https://prove2.me/theorems/5426791f-76ec-472c-b26b-7c938f4beb32
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list
-- statement:
--   For prepared pair 46, left list, the selected-floor certificate succeeds for at most `137` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Heads 0 through 136; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000.lean, lines 14-50, SHA-256 380c7dc6a60d9ae7dca3f4f36b4f51475b8794d300bf0a55c96a71cbdc5caf65. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 137
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
