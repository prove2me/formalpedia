-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:00.029935+00:00
-- url     : https://prove2.me/theorems/910a2131-810d-4db0-b4fe-fa419992fccf
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 6
-- statement:
--   For prepared pair 21, right list, part 6, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 72 through 81, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_000Part06.lean, lines 10-14, SHA-256 9e5870a1cf69ce8a89e479ecc24cc3bd425348eef8e5fc1a3491d02f388c3f5b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 10
      (PairLightPrepared21.rightCached.drop 72) (PairLightPrepared21.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
