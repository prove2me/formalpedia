-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:14.606982+00:00
-- url     : https://prove2.me/theorems/f5ce69e7-d6c9-4887-8ce5-34fba6adcc89
-- title:
--   Selected-floor prefix certificate for prepared pair 18, right list, part 3
-- statement:
--   For prepared pair 18, right list, part 3, the selected-floor certificate succeeds for at most `131` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Original heads 131 through 261; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight18_000Part03.lean, lines 7-11, SHA-256 d445be51b4edf621cd4419e9dc0419a75a06e5a02e3d0d4a865dcb416ba1a002. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 131
      (rightCached000.drop 131) (rightRows000.drop 131) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
