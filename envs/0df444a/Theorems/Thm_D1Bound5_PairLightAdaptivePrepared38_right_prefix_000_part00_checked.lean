-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:33.374992+00:00
-- url     : https://prove2.me/theorems/4a1ab9ef-365c-4233-93a9-c11cf8f506b8
-- title:
--   Selected-floor prefix certificate for prepared pair 38, right list, part 0
-- statement:
--   For prepared pair 38, right list, part 0, the selected-floor certificate succeeds for at most `38` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 0 through 37; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight38_000Part00.lean, lines 7-11, SHA-256 a4b9bdd46e4e5a453cc02c3cb097b3bb013a28305eecb589f33634ad866782b3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 38
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
