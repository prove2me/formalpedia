-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared42_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared42.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:04.65477+00:00
-- url     : https://prove2.me/theorems/b68d0347-e9ab-4ae2-9a23-baeab2f9d1eb
-- title:
--   Selected-floor prefix certificate for prepared pair 42, left list
-- statement:
--   For prepared pair 42, left list, the selected-floor certificate succeeds for at most `242` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared42.sieve`. Heads 0 through 241; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft42_000.lean, lines 7-11, SHA-256 8ef8f2244fc1d3921ca2fc63777a10b61b48394613fef769149f4f98eaa6a4e4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData42_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared42.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared42.sieve 242
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared42
end
