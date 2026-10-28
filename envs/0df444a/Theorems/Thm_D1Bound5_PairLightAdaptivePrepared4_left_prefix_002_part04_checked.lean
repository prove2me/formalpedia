-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:56.96382+00:00
-- url     : https://prove2.me/theorems/d68542d3-6bfe-4573-a571-539a0334fc01
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 4
-- statement:
--   For prepared pair 4, left list, part 4, the selected-floor certificate succeeds for at most `18` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 218 through 235, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_002Part04.lean, lines 11-16, SHA-256 45b2f437b75827c8e6196ccfcd3beb85f375d95d40f3d82552c7970da13c8ce0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 18
      (PairLightPrepared4.leftCached.drop 218)
      (PairLightPrepared4.leftRows.drop 218) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
