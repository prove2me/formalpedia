-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:18.107997+00:00
-- url     : https://prove2.me/theorems/fe1828ad-89fa-4a5b-86d2-de10ab6f1e87
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 8
-- statement:
--   For prepared pair 7, left list, part 8, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 96 through 104, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_000Part08.lean, lines 11-16, SHA-256 9b877b49ff1ea49849782feff23df556b0e610392f6ba36ca4c83c8c1870252e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 9
      (PairLightPrepared7.leftCached.drop 96)
      (PairLightPrepared7.leftRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
