-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:16.780296+00:00
-- url     : https://prove2.me/theorems/fd039d1c-c159-44cb-ab10-9b711543db3f
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 4
-- statement:
--   For prepared pair 17, left list, part 4, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 134 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_000Part04.lean, lines 7-11, SHA-256 ab55c2df3d855e0bdd8265322ebf2b3aa5565b83c7fba1b100b119154fc430c3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
