-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:40.441218+00:00
-- url     : https://prove2.me/theorems/01432b6f-b828-45b8-a945-4294ffeb40be
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 1
-- statement:
--   For prepared pair 28, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 94 through 105, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_001Part01.lean, lines 10-14, SHA-256 594e26176970afdc73637478fe77e6981461b2f9292944aa0395823a5ce05d11. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 94) (PairLightPrepared28.leftRows.drop 94) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
