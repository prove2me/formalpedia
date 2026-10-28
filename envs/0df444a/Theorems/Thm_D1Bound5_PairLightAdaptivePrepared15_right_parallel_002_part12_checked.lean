-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:22.204566+00:00
-- url     : https://prove2.me/theorems/8532a1c5-0f8e-4cea-bbb8-f7611561c4e5
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 12
-- statement:
--   For prepared pair 15, right list, part 12, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 358 through 369, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part12.lean, lines 10-14, SHA-256 c938dd9ddce4b865e10c8f786ce0a9f4987416a144e02353d9ef0c8996509f2a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part12_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 358) (PairLightPrepared15.rightRows.drop 358) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
