-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:51.600833+00:00
-- url     : https://prove2.me/theorems/93007aca-c3fa-489a-a64e-a98c15df9a21
-- title:
--   Selected-floor prefix certificate for prepared pair 12, left list, part 2
-- statement:
--   For prepared pair 12, left list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 60 through 94; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft12_000Part02.lean, lines 7-11, SHA-256 fcb71753e58b5d8e468a9bf1826a5097b6a161e8d933defaa68040b0c73ef3a1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 35
      (leftCached000.drop 60) (leftRows000.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
