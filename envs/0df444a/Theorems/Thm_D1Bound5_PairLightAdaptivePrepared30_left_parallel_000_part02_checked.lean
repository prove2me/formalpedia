-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:15.53089+00:00
-- url     : https://prove2.me/theorems/a3018ac9-30e5-49e5-9a7f-411388d07646
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 2
-- statement:
--   For prepared pair 30, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 24 through 35, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_000Part02.lean, lines 10-14, SHA-256 7ca856efdef610269cc69147b609fb9a69afab46f2a27f53f2fb612204824079. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 24) (PairLightPrepared30.leftRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
