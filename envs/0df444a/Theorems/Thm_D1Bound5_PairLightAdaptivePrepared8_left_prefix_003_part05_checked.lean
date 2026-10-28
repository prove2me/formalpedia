-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:30.307365+00:00
-- url     : https://prove2.me/theorems/42f54ece-9102-4b0d-a4e3-84a882b3ce3d
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 5
-- statement:
--   For prepared pair 8, left list, part 5, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 260 through 273, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_003Part05.lean, lines 11-16, SHA-256 399011562e74cb54a7b07e8ba691abf863c3a16af3f92521d16f1235bc857369. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.leftCached.drop 260)
      (PairLightPrepared8.leftRows.drop 260) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
