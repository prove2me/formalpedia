-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:52.373632+00:00
-- url     : https://prove2.me/theorems/bc698647-8bba-4127-9f66-7944811163d8
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 1
-- statement:
--   For prepared pair 46, right list, part 1, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 16 through 35, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_000Part01.lean, lines 7-11, SHA-256 30dc3bb12ac31a5a923a46b19d10ff747e290a03bfa820aff74a60ecc5f6baa5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 20
      (rightCached000.drop 16) (rightRows000.drop 16) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
