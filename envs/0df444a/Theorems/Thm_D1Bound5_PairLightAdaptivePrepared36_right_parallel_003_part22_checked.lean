-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part22_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:27.014523+00:00
-- url     : https://prove2.me/theorems/41ef34c9-0ad5-4ce0-83be-817ca3f020ef
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 22
-- statement:
--   For prepared pair 36, right list, part 22, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 551 through 559, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_003Part22.lean, lines 10-14, SHA-256 3cd2b128333d27808ae0ce2f856f1ed0369e185e4a5e5953ab167d731e818cfd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part22_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 9
      (PairLightPrepared36.rightCached.drop 551) (PairLightPrepared36.rightRows.drop 551) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
