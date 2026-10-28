-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:43.853065+00:00
-- url     : https://prove2.me/theorems/9dc69abd-4aed-4bb2-8fae-e50dc636d420
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list
-- statement:
--   For prepared pair 43, left list, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft43Prefix000.lean, lines 15-62, SHA-256 5447ad2fec26d68efd2793cf8be45b0c80a794afb3b74956c475d7e2c1ce6363. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 91
      PairLightPrepared43.leftCached PairLightPrepared43.leftRows = true := by sorry
end D1Bound5.PairLightAdaptivePrepared43
end
