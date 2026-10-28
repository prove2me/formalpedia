-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:24.054311+00:00
-- url     : https://prove2.me/theorems/50ff1ef1-8d1c-44e2-83a7-804bac786135
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 10
-- statement:
--   For prepared pair 26, left list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 736 through 747; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_007Part10.lean, lines 7-11, SHA-256 99c42930feb1341bc71577ccf89a272a4f86af626c64d3a8cc6ed71007186220. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached007.drop 120) (leftRows007.drop 120) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
