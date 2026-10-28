-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:30.026681+00:00
-- url     : https://prove2.me/theorems/e65b4487-e09d-4d66-a4d5-8679ed39a0e4
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 5
-- statement:
--   For prepared pair 10, left list, part 5, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 139 through 152, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_001Part05.lean, lines 11-16, SHA-256 ba294a77d1eb43bd0d581e6ca3a368775ae6a6194069a7447fe0d9e379ad0542. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 14
      (PairLightPrepared10.leftCached.drop 139)
      (PairLightPrepared10.leftRows.drop 139) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
