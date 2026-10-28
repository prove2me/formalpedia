-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:13.064934+00:00
-- url     : https://prove2.me/theorems/283778cb-78a4-4053-a43e-07b3ad997ab8
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 13
-- statement:
--   For prepared pair 28, right list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 491 through 502, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part13.lean, lines 10-14, SHA-256 c17532c433b3e99cdaf6bab7ae1ef35fee73fcfd1f71594f061458c9db0890fd. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 491) (PairLightPrepared28.rightRows.drop 491) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
