-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:58.571655+00:00
-- url     : https://prove2.me/theorems/51902f66-ec49-4aaa-b667-2aefe97a14af
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 2
-- statement:
--   For prepared pair 36, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 24 through 35, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_000Part02.lean, lines 10-14, SHA-256 069ebb051d3b380454cb648f6f9db698a1bff2254df452bf4cfa2f404d9db986. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 24) (PairLightPrepared36.leftRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
