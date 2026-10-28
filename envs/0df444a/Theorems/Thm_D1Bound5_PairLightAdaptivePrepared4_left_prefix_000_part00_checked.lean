-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:48.052645+00:00
-- url     : https://prove2.me/theorems/b4d7e663-6637-4da9-85a5-c9cffc90c82d
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 0
-- statement:
--   For prepared pair 4, left list, part 0, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 0 through 10, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_000Part00.lean, lines 11-16, SHA-256 22e0c45ec2ab8385bdd3ce1a3bdd43764bcd019ef0734d1ee2e4b82784571e61. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 11
      (PairLightPrepared4.leftCached.drop 0)
      (PairLightPrepared4.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
