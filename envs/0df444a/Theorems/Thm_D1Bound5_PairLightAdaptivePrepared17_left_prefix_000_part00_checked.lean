-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:33.909202+00:00
-- url     : https://prove2.me/theorems/2e806039-f720-460b-a08f-cc3a6c0642e5
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 0
-- statement:
--   For prepared pair 17, left list, part 0, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 0 through 27; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_000Part00.lean, lines 7-11, SHA-256 81d30efb3a255b6e7c6936a47c9d3a1a754321840ffb5bb33c27ff16c8b066e1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 28
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
