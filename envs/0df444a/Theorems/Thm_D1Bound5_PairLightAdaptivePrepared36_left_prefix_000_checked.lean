-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:53.367233+00:00
-- url     : https://prove2.me/theorems/3e0d1af0-e91f-4a08-87c4-fda5860f6472
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list
-- statement:
--   For prepared pair 36, left list, the selected-floor certificate succeeds for at most `76` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft36_000.lean, lines 15-56, SHA-256 48b46f243f0e6a1078e3bd5e5320e14df2748c1a6e87f195fa21cae8392ceb7b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 76
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
