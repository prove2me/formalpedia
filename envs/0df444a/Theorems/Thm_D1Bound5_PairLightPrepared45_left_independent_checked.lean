-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared45_left_independent_checked
-- name    : D1Bound5.PairLightPrepared45.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:44:57.974098+00:00
-- url     : https://prove2.me/theorems/2cd8688a-a93c-4848-9524-a1400a6c0299
-- title:
--   Pair Light Prepared45 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared45.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft45.lean, lines 19-39, SHA-256 47e2e790515197caaccee85d3feeb74bcb1b526f3ce117c71ccdb0f659913262. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared45.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 5 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared45
end
