-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:50.730672+00:00
-- url     : https://prove2.me/theorems/c0ad5fa0-3a81-4b67-b932-73678bc879d4
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list
-- statement:
--   For prepared pair 4, left list, the selected-floor certificate succeeds for at most `82` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_001.lean, lines 15-50, SHA-256 89c2860e6fb39f810a2a4464fbd22536085afbdb703472cbda2f247fa8255dae. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 82
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
