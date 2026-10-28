-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_002_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:10.204243+00:00
-- url     : https://prove2.me/theorems/1824e9ca-26ab-4849-a281-fc5cc9b5da92
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 10
-- statement:
--   For prepared pair 28, right list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 304 through 315, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_002Part10.lean, lines 10-14, SHA-256 385a4e3e949fd38dd6e5b5844b12b3a3c71cdc853dcc03d25e42db5367ded8bd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 304) (PairLightPrepared28.rightRows.drop 304) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
