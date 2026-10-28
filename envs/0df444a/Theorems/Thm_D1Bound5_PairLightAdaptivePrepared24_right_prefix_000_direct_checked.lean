-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:48:15.408339+00:00
-- url     : https://prove2.me/theorems/58c0119f-839c-4bec-9c6f-1565a23f7b75
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list
-- statement:
--   For prepared pair 24, right list, the selected-floor certificate succeeds for at most `101` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight24Prefix000.lean, lines 16-69, SHA-256 a074cb297e05d10c9870015abafa383c3790ba66050acc7f402b9319f703d377. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 101
      (PairLightPrepared24.rightCached.drop 0) (PairLightPrepared24.rightRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared24
end
