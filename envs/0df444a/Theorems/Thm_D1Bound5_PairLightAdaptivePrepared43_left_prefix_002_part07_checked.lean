-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:00.819828+00:00
-- url     : https://prove2.me/theorems/f0a16d25-14f8-4ad1-8648-a2fb55d944c4
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 7
-- statement:
--   For prepared pair 43, left list, part 7, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 380 through 403, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_002Part07.lean, lines 8-13, SHA-256 efe36dcf7a2e435bbba1090233e94bf97738fab71263b33741e20829c2ec5d54. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.leftCached.drop 380)
      (PairLightPrepared43.leftRows.drop 380) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
