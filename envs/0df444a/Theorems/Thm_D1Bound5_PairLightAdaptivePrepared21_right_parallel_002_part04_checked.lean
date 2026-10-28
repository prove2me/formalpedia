-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:52.366125+00:00
-- url     : https://prove2.me/theorems/8d85f90b-3fd3-4805-820b-4dbb60f39bb9
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 4
-- statement:
--   For prepared pair 21, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 232 through 243, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_002Part04.lean, lines 10-14, SHA-256 9ccd19e58a2f19933f92adc87820af617d209aa7d8f5f51ddec4e5ad33619fb0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 232) (PairLightPrepared21.rightRows.drop 232) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
