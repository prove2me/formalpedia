-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:48.171651+00:00
-- url     : https://prove2.me/theorems/355122aa-1321-4eb4-aa7a-f0070057a80f
-- title:
--   Selected-floor prefix certificate for prepared pair 29, right list, part 1
-- statement:
--   For prepared pair 29, right list, part 1, the selected-floor certificate succeeds for at most `26` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 24 through 49, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight29_000Part01.lean, lines 7-11, SHA-256 c80c59614eff655b9183ace6304529c37bdf17ee77eebe3d29533285264302ec. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 26
      (rightCached000.drop 24) (rightRows000.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
