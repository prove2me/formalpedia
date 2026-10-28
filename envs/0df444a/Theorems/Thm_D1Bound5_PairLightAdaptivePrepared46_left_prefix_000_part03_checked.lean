-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:58.737319+00:00
-- url     : https://prove2.me/theorems/db7862f6-237b-4de2-85de-75f8aad9b091
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 3
-- statement:
--   For prepared pair 46, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 58 through 81, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000Part03.lean, lines 7-11, SHA-256 8bd62df93ec2f296a1c94e835924714d03c2c94c8b100eabd377f5c153825122. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 24
      (leftCached000.drop 58) (leftRows000.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
