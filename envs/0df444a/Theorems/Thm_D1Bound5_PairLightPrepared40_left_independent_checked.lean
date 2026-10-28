-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared40_left_independent_checked
-- name    : D1Bound5.PairLightPrepared40.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:22:24.927988+00:00
-- url     : https://prove2.me/theorems/3a217920-715c-4de9-af98-a60c6d568231
-- title:
--   Pair Light Prepared40 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared40.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft40.lean, lines 18-33, SHA-256 bfd270701140b8217ffca2c5bf17fa40c60056332b14d22eb7351596f71448e0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_003

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared40.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared40
end
