-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:37.4803+00:00
-- url     : https://prove2.me/theorems/144fe2a7-efa5-4103-8367-e59284077e4a
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list
-- statement:
--   For prepared pair 6, left list, the selected-floor certificate succeeds for at most `189` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_005.lean, lines 13-36, SHA-256 0b5ef741e649c8edcc3381aa03d6b1ab03621226d88c6941f5bea3022d314a5c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 189
      leftCached005 leftRows005 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
