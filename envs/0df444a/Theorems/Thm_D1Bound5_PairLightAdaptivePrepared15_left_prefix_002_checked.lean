-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:40:21.946628+00:00
-- url     : https://prove2.me/theorems/46cc314c-f476-4e80-a7b8-377211e41008
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list
-- statement:
--   For prepared pair 15, left list, the selected-floor certificate succeeds for at most `267` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft15_002.lean, lines 31-168, SHA-256 6ad951b67e2ba0f4b4928e395464331c149dd8fd69a4fe819726625bb252714c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 267
      leftCached002 leftRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
