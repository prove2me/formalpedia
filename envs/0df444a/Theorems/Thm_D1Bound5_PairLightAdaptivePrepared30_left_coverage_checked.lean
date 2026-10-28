-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:35:35.67037+00:00
-- url     : https://prove2.me/theorems/c5b26eec-f515-446b-a7bc-ee3a0c8ca685
-- title:
--   Pair Light Adaptive Prepared30 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared30.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation30.lean, lines 7-9, SHA-256 11a024af2a26b4ebfc0a85daa7b7597218e5054c96e234a4d05934a663f33464. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_coverage_checked :
    decide (PairLightPrepared30.leftCached.map Prod.fst = PairLightPrepared30.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared30
end
