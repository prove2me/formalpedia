-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:19.367885+00:00
-- url     : https://prove2.me/theorems/427a9460-b636-4119-a85c-09196f583ef6
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list
-- statement:
--   For prepared pair 19, right list, the selected-floor certificate succeeds for at most `101` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight19Prefix000.lean, lines 16-69, SHA-256 0784c8b918867c45f7bc1df8b3ec481ba5f14f35566fce50c39dd9e293e275e1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 101
      (PairLightPrepared19.rightCached.drop 0) (PairLightPrepared19.rightRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared19
end
