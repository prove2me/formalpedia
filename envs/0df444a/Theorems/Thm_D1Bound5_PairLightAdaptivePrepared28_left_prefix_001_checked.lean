-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:55.86974+00:00
-- url     : https://prove2.me/theorems/0f4a7aba-6063-4f4c-af58-1f6dc07dfb6e
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list
-- statement:
--   For prepared pair 28, left list, the selected-floor certificate succeeds for at most `102` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft28_001.lean, lines 17-70, SHA-256 c63762121482e9f0302423294b89a6fba5ccb42fd54f11ed0a8e0027da3626dd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 102
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
