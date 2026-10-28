-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:10:53.11199+00:00
-- url     : https://prove2.me/theorems/153ac8ec-2dcf-4dad-b315-e6f2f7745f74
-- title:
--   Pair Light Adaptive Prepared21 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared21.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation21.lean, lines 7-9, SHA-256 8926dc2071f521b1b3c2b556d7d3f2e7e770b9cdabead72da2dd9587d4c5a46f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_coverage_checked :
    decide (PairLightPrepared21.leftCached.map Prod.fst = PairLightPrepared21.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared21
end
