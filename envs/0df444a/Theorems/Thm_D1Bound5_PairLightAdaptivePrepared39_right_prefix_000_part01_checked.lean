-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:56:44.674353+00:00
-- url     : https://prove2.me/theorems/40e559c9-eaeb-4f46-bcff-e38e6738ec92
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 1
-- statement:
--   For prepared pair 39, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 12 through 23, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_000Part01.lean, lines 11-16, SHA-256 bdbc35ceb12ac1c125662812733ef60b38d2f92e6a1d76e3fc53f7e5f9fab6fe. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.rightCached.drop 12)
      (PairLightPrepared39.rightRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
