-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:18.692047+00:00
-- url     : https://prove2.me/theorems/bc5c34da-63ec-4dce-ba64-838124d09be7
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list
-- statement:
--   For prepared pair 24, left list, the selected-floor certificate succeeds for at most `198` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft24Prefix002.lean, lines 16-69, SHA-256 9123cc3aa672536d934ec624572e14b8f0aee7d82cef789e33eebbf3fa482ac1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 198
      (PairLightPrepared24.leftCached.drop 248) (PairLightPrepared24.leftRows.drop 248) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared24
end
