-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared38_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared38.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:14:50.794404+00:00
-- url     : https://prove2.me/theorems/121867ce-2aa9-433e-835a-feaf620f0467
-- title:
--   Pair Light Prepared38 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared38.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight38.lean, lines 9-11, SHA-256 4124fc847de5ef6d667df883652750a2c8c5beac8946c20a5f389b2ad11f6881. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared38.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared38
end
