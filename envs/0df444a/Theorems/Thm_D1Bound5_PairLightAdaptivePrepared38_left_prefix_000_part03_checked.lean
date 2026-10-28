-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:08.390085+00:00
-- url     : https://prove2.me/theorems/1000fc0c-e239-4c93-998f-23c03603372c
-- title:
--   Selected-floor prefix certificate for prepared pair 38, left list, part 3
-- statement:
--   For prepared pair 38, left list, part 3, the selected-floor certificate succeeds for at most `140` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 140 through 279; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft38_000Part03.lean, lines 7-11, SHA-256 a5512738126a53ce287b135865dcafd56791e4ca341b7fc99a272c5200369439. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 140
      (leftCached000.drop 140) (leftRows000.drop 140) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
