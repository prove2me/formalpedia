-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:22.412981+00:00
-- url     : https://prove2.me/theorems/6e6ce2de-cd32-493e-b687-cdb335b451e7
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list
-- statement:
--   For prepared pair 29, left list, the selected-floor certificate succeeds for at most `126` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_000.lean, lines 13-42, SHA-256 28b8c0013b9775daa25423e1211309390ebbb0ab1a0cf96a64199701ddc1646d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 126
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
