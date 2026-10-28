-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:13.443518+00:00
-- url     : https://prove2.me/theorems/f3f23466-fbcb-4a18-a280-e98b26c9270f
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list
-- statement:
--   For prepared pair 8, right list, the selected-floor certificate succeeds for at most `63` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_001.lean, lines 15-50, SHA-256 2aa43725ddb72aba43922ce3b36e5509363c7c5ecf09f3054649d17d4684d26f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 63
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
