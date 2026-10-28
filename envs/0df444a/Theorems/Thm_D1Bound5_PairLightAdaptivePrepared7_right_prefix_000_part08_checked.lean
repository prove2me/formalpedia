-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:17.865168+00:00
-- url     : https://prove2.me/theorems/7b6f92b2-9b77-4c43-8b0f-b67aca321b74
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 8
-- statement:
--   For prepared pair 7, right list, part 8, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 96 through 105, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_000Part08.lean, lines 11-16, SHA-256 5be9b23a2e5e253091fee3aa59097e198767e46d81551f32f8f850ab44c3eb85. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 10
      (PairLightPrepared7.rightCached.drop 96)
      (PairLightPrepared7.rightRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
