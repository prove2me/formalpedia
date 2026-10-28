-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:29.793318+00:00
-- url     : https://prove2.me/theorems/14eb1be8-7be9-4a52-8778-76016bdd9bdc
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 0
-- statement:
--   For prepared pair 4, left list, part 0, the selected-floor certificate succeeds for at most `15` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 153 through 167, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_002Part00.lean, lines 11-16, SHA-256 2315b91be5927e7e5d05770ecac5a6e125f83f1330c57b518cd4c614a99cd6e2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 15
      (PairLightPrepared4.leftCached.drop 153)
      (PairLightPrepared4.leftRows.drop 153) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
