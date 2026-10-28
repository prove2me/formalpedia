-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:50.571323+00:00
-- url     : https://prove2.me/theorems/6ea9248f-d3db-455c-9883-077eb457d9f9
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 6
-- statement:
--   For prepared pair 7, right list, part 6, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 416 through 429, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_002Part06.lean, lines 11-16, SHA-256 e3ff61c98c1e7bd20cad633925796f2b0b2944e26a0acd459aea357fc603707d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 14
      (PairLightPrepared7.rightCached.drop 416)
      (PairLightPrepared7.rightRows.drop 416) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
