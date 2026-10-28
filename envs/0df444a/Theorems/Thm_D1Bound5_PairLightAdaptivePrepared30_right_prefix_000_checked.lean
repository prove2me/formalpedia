-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:07.781536+00:00
-- url     : https://prove2.me/theorems/f2c7f50b-ade3-4eaa-a6a0-09458cb204d5
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list
-- statement:
--   For prepared pair 30, right list, the selected-floor certificate succeeds for at most `92` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight30_000.lean, lines 16-63, SHA-256 9fb2bd57974a0f2dc7b9070789f4d8cb621a9d7ec9bd0b0e71d60246cbe401d5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 92
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
