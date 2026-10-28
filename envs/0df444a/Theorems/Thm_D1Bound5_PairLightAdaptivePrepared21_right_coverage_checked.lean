-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:24:34.797259+00:00
-- url     : https://prove2.me/theorems/591c8951-7afc-43f9-97c3-ad16465a5ecc
-- title:
--   Pair Light Adaptive Prepared21 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared21.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation21.lean, lines 16-18, SHA-256 8926dc2071f521b1b3c2b556d7d3f2e7e770b9cdabead72da2dd9587d4c5a46f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_coverage_checked :
    decide (PairLightPrepared21.rightCached.map Prod.fst = PairLightPrepared21.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared21
end
