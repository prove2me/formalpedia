-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_000_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:26.681007+00:00
-- url     : https://prove2.me/theorems/d87dabd3-c820-45a7-9d15-bb2a555f912a
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list
-- statement:
--   For prepared pair 7, left list, the selected-floor certificate succeeds for at most `105` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft7Prefix000.lean, lines 16-69, SHA-256 24954ed9ba19f55a2a4d7ffc3659bbaf2c581a53991faa2f5f21194ad0f8a208. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 105
      (PairLightPrepared7.leftCached.drop 0) (PairLightPrepared7.leftRows.drop 0) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared7
end
