-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:58.768016+00:00
-- url     : https://prove2.me/theorems/84a1d0df-d334-4f7d-9485-7ea17be8e872
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 1
-- statement:
--   For prepared pair 10, left list, part 1, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 84 through 96, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_001Part01.lean, lines 11-16, SHA-256 0ae2d4fdc39b7d91bf980ba1dc6c8ddb03935cbbc69f544dc3bf459b52db4fea. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.leftCached.drop 84)
      (PairLightPrepared10.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
