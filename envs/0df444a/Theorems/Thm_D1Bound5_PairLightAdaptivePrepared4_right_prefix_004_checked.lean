-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:29.503981+00:00
-- url     : https://prove2.me/theorems/b9d57677-52eb-41ed-bd2b-f6f9cd10d705
-- title:
--   Selected-floor prefix certificate for prepared pair 4, right list
-- statement:
--   For prepared pair 4, right list, the selected-floor certificate succeeds for at most `191` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight4_004.lean, lines 13-36, SHA-256 bde0205f9759aae71a1b84dbef58a9b75b5d65bd45a7e99b797872750f3a117f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 191
      rightCached004 rightRows004 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
