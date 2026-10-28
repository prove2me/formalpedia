-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:59.417985+00:00
-- url     : https://prove2.me/theorems/77e6ad40-0f55-419c-b794-9825b4d8012e
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 4
-- statement:
--   For prepared pair 30, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 140 through 151, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_001Part04.lean, lines 10-14, SHA-256 f9c3648da1d1c040ddb52bcb2e7276f3798010cda3e4339e595a902f2fb97626. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 140) (PairLightPrepared30.rightRows.drop 140) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
