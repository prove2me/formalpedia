-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:50.448715+00:00
-- url     : https://prove2.me/theorems/a9eb5159-0fbf-4f6a-96d3-ec86041527ef
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list
-- statement:
--   For prepared pair 8, left list, the selected-floor certificate succeeds for at most `82` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_003.lean, lines 15-50, SHA-256 9c35133aa8c5b9a075e0c4d9f5a67802ce5c4547752d467d35cfb2c8853c500d. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 82
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
