-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:46.26993+00:00
-- url     : https://prove2.me/theorems/875ca5f0-9256-444d-9712-1f0d2d1db0c3
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 3
-- statement:
--   For prepared pair 24, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 36 through 47, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_000Part03.lean, lines 11-16, SHA-256 49ee2e147844fb0c9196f5df0acf83f52e2ae3ac81906b4d6dfb081fcae4b33c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.rightCached.drop 36)
      (PairLightPrepared24.rightRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
