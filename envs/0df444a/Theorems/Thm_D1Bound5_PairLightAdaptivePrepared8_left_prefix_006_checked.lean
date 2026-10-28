-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:36.215107+00:00
-- url     : https://prove2.me/theorems/89e55cb6-b689-4058-92a5-d3a7191e7996
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list
-- statement:
--   For prepared pair 8, left list, the selected-floor certificate succeeds for at most `189` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_006.lean, lines 13-36, SHA-256 97c18727f6364fbc38ab8ea5557e440a3f5453d059785b4fc793a69332bc8236. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 189
      leftCached006 leftRows006 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
