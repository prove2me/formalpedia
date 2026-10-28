-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:57.695194+00:00
-- url     : https://prove2.me/theorems/1b8b662e-3a83-47e4-a7a2-d408d1af8f80
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 2
-- statement:
--   For prepared pair 5, left list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 317 through 340, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_002Part02.lean, lines 11-16, SHA-256 a6710df9d00d6bf4787c09beb3fefb0dde9ec329cddff42bd6be44cc750d8fca. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 317)
      (PairLightPrepared5.leftRows.drop 317) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
