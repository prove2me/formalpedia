-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:30.028859+00:00
-- url     : https://prove2.me/theorems/aa444dca-898b-4190-a416-60afab428749
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list
-- statement:
--   For prepared pair 10, left list, the selected-floor certificate succeeds for at most `82` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_001.lean, lines 15-50, SHA-256 c16051d23f6ec465db524d7896888b083d006ea74f0f656f98dee0751ea37e6e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 82
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
