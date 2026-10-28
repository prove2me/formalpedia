-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:38.964997+00:00
-- url     : https://prove2.me/theorems/35f5770e-4edd-45f3-8296-2841481abce8
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 3
-- statement:
--   For prepared pair 4, left list, part 3, the selected-floor certificate succeeds for at most `17` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 201 through 217, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_002Part03.lean, lines 11-16, SHA-256 64b60503c365a779e38d62d93404f47827f6f310497d2792ea8f2fe20633a03c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 17
      (PairLightPrepared4.leftCached.drop 201)
      (PairLightPrepared4.leftRows.drop 201) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
