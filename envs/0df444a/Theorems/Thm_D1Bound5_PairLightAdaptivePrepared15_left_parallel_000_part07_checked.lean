-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:53.890038+00:00
-- url     : https://prove2.me/theorems/f4895f3b-2497-4f99-8cca-596f1fdfc128
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 7
-- statement:
--   For prepared pair 15, left list, part 7, the selected-floor certificate succeeds for at most `8` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 84 through 91, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_000Part07.lean, lines 10-14, SHA-256 6347cdf4f9cd9b6590964f0c57a191813d445cdf6acee59b01c7d956c8df69f1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part07_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 8
      (PairLightPrepared15.leftCached.drop 84) (PairLightPrepared15.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
