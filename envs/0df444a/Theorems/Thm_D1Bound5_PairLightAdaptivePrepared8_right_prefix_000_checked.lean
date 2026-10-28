-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:49:54.781965+00:00
-- url     : https://prove2.me/theorems/006aca48-adf7-4913-908b-fcf0a80bcab0
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list
-- statement:
--   For prepared pair 8, right list, the selected-floor certificate succeeds for at most `58` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_000.lean, lines 15-50, SHA-256 b2d37bf1ba24abe9bfe9bfff1d603844741fa6fa72d11e647b890b36889ac599. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 58
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
