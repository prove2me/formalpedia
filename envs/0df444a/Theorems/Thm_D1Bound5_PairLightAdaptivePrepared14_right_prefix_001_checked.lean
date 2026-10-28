-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:44:53.79591+00:00
-- url     : https://prove2.me/theorems/c2444fc4-dd4b-4e83-bfa2-f1b1149c969a
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list
-- statement:
--   For prepared pair 14, right list, the selected-floor certificate succeeds for at most `114` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight14_001.lean, lines 18-77, SHA-256 8d5e4c36e23672324698040d308dd569a6b54894170c17b4317e0d7aa2396fe3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 114
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
