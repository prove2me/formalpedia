-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part21_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part21_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:37.098665+00:00
-- url     : https://prove2.me/theorems/03c2e809-42f8-4d40-99ce-ef39663e9d5b
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 21
-- statement:
--   For prepared pair 23, right list, part 21, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 466 through 477, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part21.lean, lines 10-14, SHA-256 c4581f85c8e3bb1dd0c8b189948ecce9dfab349023647ae2a16a44c82720559b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part21_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 466) (PairLightPrepared23.rightRows.drop 466) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
