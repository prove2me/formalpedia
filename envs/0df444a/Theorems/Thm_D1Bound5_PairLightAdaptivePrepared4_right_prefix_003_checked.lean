-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_003_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:31.405302+00:00
-- url     : https://prove2.me/theorems/21f853f7-7e17-45be-9a3b-8329a9194722
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list
-- statement:
--   For prepared pair 4, right list, the selected-floor certificate succeeds for at most `150` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_003.lean, lines 16-57, SHA-256 2ef0406cefd1e89a696bdd961aafa75bd49a3e3f1f3e84d763d7c60b2f0f0c8f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 150
      rightCached003 rightRows003 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
