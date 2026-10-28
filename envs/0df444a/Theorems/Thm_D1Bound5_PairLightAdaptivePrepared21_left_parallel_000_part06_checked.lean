-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:04.349144+00:00
-- url     : https://prove2.me/theorems/6c54e2b9-7f9e-4bab-aef0-1b433b04380b
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 6
-- statement:
--   For prepared pair 21, left list, part 6, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 72 through 81, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_000Part06.lean, lines 10-14, SHA-256 c5bdc3765844f0d1da0de8c50afe26b38e367a458150051161b2f0487fa64f02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 10
      (PairLightPrepared21.leftCached.drop 72) (PairLightPrepared21.leftRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
