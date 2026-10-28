-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:50.572308+00:00
-- url     : https://prove2.me/theorems/dba4ce3b-3de9-4826-bfa1-6019f4cdb534
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list
-- statement:
--   For prepared pair 30, right list, the selected-floor certificate succeeds for at most `266` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight30_002.lean, lines 31-168, SHA-256 7bd1e2d02a790dbbae0b3b55adf71ac1f5927560800017cf4a7cabfa93cfe702. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 266
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
