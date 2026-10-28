-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:01.73848+00:00
-- url     : https://prove2.me/theorems/38aa7f5b-81e0-406c-9e26-870b9e7c50a7
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 3
-- statement:
--   For prepared pair 26, left list, part 3, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 122 through 124; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part03.lean, lines 7-11, SHA-256 22da77c28f29ad1930712de0e372306ca62102fb1d6cae64b6d21d8bf30f0214. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 9) (leftRows002.drop 9) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
