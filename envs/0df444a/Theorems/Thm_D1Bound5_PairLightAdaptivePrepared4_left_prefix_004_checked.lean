-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:20.566244+00:00
-- url     : https://prove2.me/theorems/0cddde3a-7cce-40a1-a576-9c393161db18
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list
-- statement:
--   For prepared pair 4, left list, the selected-floor certificate succeeds for at most `191` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_004.lean, lines 13-36, SHA-256 1b63f3525af2718a156422c122b9420e2db6b99bf638f8ab2a674c74c8bde83d. Project: https://github.com/tomislav-math/d1-bound5-lean

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

theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 191
      leftCached004 leftRows004 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
