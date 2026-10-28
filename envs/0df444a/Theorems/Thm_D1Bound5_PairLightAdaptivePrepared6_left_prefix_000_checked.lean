-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:35.441098+00:00
-- url     : https://prove2.me/theorems/6ef93ff6-95ec-429e-8a28-a24c0e6708e2
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list
-- statement:
--   For prepared pair 6, left list, the selected-floor certificate succeeds for at most `63` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_000.lean, lines 15-50, SHA-256 48ca0f1b6a168b6c0a35b4d70e1ad3e78b57afb33d9a5f061d836b3e8a82e614. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 63
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
