-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:06.276393+00:00
-- url     : https://prove2.me/theorems/f1e7bc44-a9eb-4139-b128-8bdb491d305c
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list, part 3
-- statement:
--   For prepared pair 4, right list, part 3, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 111 through 124, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_001Part03.lean, lines 11-16, SHA-256 33d724b4c56a1686252bdf7b64fed0ade8c503c0ab89d2a7e377fbaf368c79e5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.rightCached.drop 111)
      (PairLightPrepared4.rightRows.drop 111) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
