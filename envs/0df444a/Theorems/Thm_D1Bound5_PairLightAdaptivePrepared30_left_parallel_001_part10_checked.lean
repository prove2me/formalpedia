-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:43.537839+00:00
-- url     : https://prove2.me/theorems/c4908300-3ffb-47b5-a473-ca86a988e864
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 10
-- statement:
--   For prepared pair 30, left list, part 10, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 211 through 211, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part10.lean, lines 10-14, SHA-256 564ad4189123dc140ed956dcc5b012e41eded924449ee2f42745ec1ec758518f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 1
      (PairLightPrepared30.leftCached.drop 211) (PairLightPrepared30.leftRows.drop 211) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
