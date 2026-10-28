-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:10.404954+00:00
-- url     : https://prove2.me/theorems/a7addecf-c1a0-45a4-921c-24d0550ae0d2
-- title:
--   Selected-floor prefix certificate for prepared pair 25, left list
-- statement:
--   For prepared pair 25, left list, the selected-floor certificate succeeds for at most `254` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared25.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft25_001.lean, lines 12-35, SHA-256 10bcd483be0ecce837fc7245b63b2fd6b36a44eee993c97af6ced289bc369916. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 254
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared25
end
