-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:14.786498+00:00
-- url     : https://prove2.me/theorems/9f8c3c9f-2098-428f-aed9-0da60e753fd1
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list
-- statement:
--   For prepared pair 10, left list, the selected-floor certificate succeeds for at most `150` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_003.lean, lines 16-57, SHA-256 6e4533753d8b7d247d2df7f106f777e6b69c8609b3e52cc34f8eafcf63d50a42. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 150
      leftCached003 leftRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
