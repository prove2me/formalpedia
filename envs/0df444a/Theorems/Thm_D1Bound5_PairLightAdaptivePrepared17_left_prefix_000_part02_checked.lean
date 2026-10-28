-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:54.24553+00:00
-- url     : https://prove2.me/theorems/9b3448c2-0dbc-4b5d-8e6f-6df51e00a880
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 2
-- statement:
--   For prepared pair 17, left list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 59 through 93; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_000Part02.lean, lines 7-11, SHA-256 814bb3b10a07970de0603367d8bf100860ea9ddfe5f23fbe7f9070b9b6c8b20f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 35
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
