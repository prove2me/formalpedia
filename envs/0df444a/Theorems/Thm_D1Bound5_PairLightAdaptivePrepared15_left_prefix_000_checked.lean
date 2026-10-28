-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:41.662005+00:00
-- url     : https://prove2.me/theorems/937d4149-4ed4-4f30-82eb-161457ac76c5
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list
-- statement:
--   For prepared pair 15, left list, the selected-floor certificate succeeds for at most `92` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft15_000.lean, lines 16-63, SHA-256 56b82d9d44784f155c50e065191175ff3ed4448dcec0d5a8d005ed52dceadff5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 92
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
