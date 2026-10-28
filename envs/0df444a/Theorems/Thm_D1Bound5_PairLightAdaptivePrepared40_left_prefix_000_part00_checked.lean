-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:08.174184+00:00
-- url     : https://prove2.me/theorems/c1f87cb9-2db9-4888-acc0-fd686d4e429c
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 0
-- statement:
--   For prepared pair 40, left list, part 0, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 0 through 27; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_000Part00.lean, lines 7-11, SHA-256 7c905b6421c0b73598f3dcdcc0976ab8fbc0756834b97d2a53f12844eff56e3a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 28
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
