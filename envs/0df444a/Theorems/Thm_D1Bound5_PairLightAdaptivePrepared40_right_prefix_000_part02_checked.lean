-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:20:22.504153+00:00
-- url     : https://prove2.me/theorems/4cd5b171-43e9-4ca6-8ac7-2470c40715a1
-- title:
--   Selected-floor prefix certificate for prepared pair 40, right list, part 2
-- statement:
--   For prepared pair 40, right list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 61 through 95; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight40_000Part02.lean, lines 7-11, SHA-256 dd155d85532924af22b4b5055aa2bca75f9881f539f37221cbe7efd3697ca23e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 35
      (rightCached000.drop 61) (rightRows000.drop 61) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
