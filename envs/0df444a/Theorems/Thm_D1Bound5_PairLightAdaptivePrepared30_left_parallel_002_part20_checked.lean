-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part20_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:56.376139+00:00
-- url     : https://prove2.me/theorems/6d89abaa-bea9-4976-ad77-c27f97f700a7
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 20
-- statement:
--   For prepared pair 30, left list, part 20, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 452 through 463, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part20.lean, lines 10-14, SHA-256 1760e95318594997f3c7671fa98c6a5ed45c615879b2ec2962efa1a02858cc82. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part20_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 452) (PairLightPrepared30.leftRows.drop 452) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
