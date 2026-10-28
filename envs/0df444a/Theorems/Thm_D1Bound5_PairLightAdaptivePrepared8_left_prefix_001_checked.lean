-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:27.595783+00:00
-- url     : https://prove2.me/theorems/89b8e357-5a1f-4231-83ff-b95bcfe872df
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list
-- statement:
--   For prepared pair 8, left list, the selected-floor certificate succeeds for at most `63` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_001.lean, lines 15-50, SHA-256 f4e0b17f85c2a5a7f3fc7089991b4c141e52f08c86f48a9e4f0c9fd2d80af6b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 63
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
