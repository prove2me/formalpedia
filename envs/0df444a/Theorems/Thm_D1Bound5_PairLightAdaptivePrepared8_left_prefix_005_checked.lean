-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:15.308325+00:00
-- url     : https://prove2.me/theorems/1e418c2a-26df-4a9d-be72-0419f32d55f9
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list
-- statement:
--   For prepared pair 8, left list, the selected-floor certificate succeeds for at most `151` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_005.lean, lines 16-57, SHA-256 a3e0ac699c3989c476a2b6c6030fb9be4ae5a5debd07aa12c2cecc5cd9596c58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 151
      leftCached005 leftRows005 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
