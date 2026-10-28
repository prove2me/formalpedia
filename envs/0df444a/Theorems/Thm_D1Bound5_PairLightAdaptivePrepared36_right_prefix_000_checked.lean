-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:07.58607+00:00
-- url     : https://prove2.me/theorems/73a66fdb-0d82-4d67-9d1d-29ed9eae0a32
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list
-- statement:
--   For prepared pair 36, right list, the selected-floor certificate succeeds for at most `76` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight36_000.lean, lines 15-56, SHA-256 5e7d441e16b437f4ea9dce496f5a14aba82f53eaf30766893ad16ca8bad60ae3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 76
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
