-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:38.002003+00:00
-- url     : https://prove2.me/theorems/dc6176c3-ee4e-4414-b1ce-6bf065c87ae1
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 2
-- statement:
--   For prepared pair 4, left list, part 2, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 97 through 110, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_001Part02.lean, lines 11-16, SHA-256 860af4aa300538a9370896e64409844b742e54329dcb2979c2264ab6c22a7d96. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.leftCached.drop 97)
      (PairLightPrepared4.leftRows.drop 97) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
