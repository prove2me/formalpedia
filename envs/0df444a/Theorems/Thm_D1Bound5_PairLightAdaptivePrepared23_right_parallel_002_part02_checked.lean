-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:57:56.16161+00:00
-- url     : https://prove2.me/theorems/2b8b31fb-e6b8-4b90-b0aa-8e436e9c7bcc
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 2
-- statement:
--   For prepared pair 23, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 238 through 249, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part02.lean, lines 10-14, SHA-256 8e210e5c5c557eb63a0fc6a8c028bb9c475d2e3911fcc7a24acd34974a58a6c4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 238) (PairLightPrepared23.rightRows.drop 238) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
