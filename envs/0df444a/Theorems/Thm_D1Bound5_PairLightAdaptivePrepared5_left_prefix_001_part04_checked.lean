-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:12.574212+00:00
-- url     : https://prove2.me/theorems/f3891a30-8f8e-4c59-bb3d-f920fc0f8ad9
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 4
-- statement:
--   For prepared pair 5, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 201 through 224, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_001Part04.lean, lines 11-16, SHA-256 9d37a9660723bd962472daa1bdab89a323d9c0b332cfef5ae9a2c1bfdc933fde. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 201)
      (PairLightPrepared5.leftRows.drop 201) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
