-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part15_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:23.512978+00:00
-- url     : https://prove2.me/theorems/1f5b0ce6-1756-4350-8b7f-d5f5344e6bc6
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 15
-- statement:
--   For prepared pair 30, right list, part 15, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 394 through 405, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part15.lean, lines 10-14, SHA-256 239613b18358eebc0a561cf40b745e39e4c4f5a3468afeb8981bdc860dc35b35. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part15_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 394) (PairLightPrepared30.rightRows.drop 394) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
