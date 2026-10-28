-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:05.38287+00:00
-- url     : https://prove2.me/theorems/1873ad3c-05cb-4848-8aed-9c78f4bff7bf
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list
-- statement:
--   For prepared pair 28, right list, the selected-floor certificate succeeds for at most `82` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight28_000.lean, lines 15-56, SHA-256 11d53366fe10f00700c4ee890f4e3fcf1f04acbcf3a574871835aae4081257ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 82
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
