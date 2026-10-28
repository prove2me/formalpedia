-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared19_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared19.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:33:05.735731+00:00
-- url     : https://prove2.me/theorems/3e3d094e-370f-410f-aab9-a9b1b87cc492
-- title:
--   Pair Light Prepared19 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared19.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft19.lean, lines 11-13, SHA-256 1b3300d74d2cca9bfee8b20a0b1ca45e7f3616ea6d7a6b981bdaf5703f4b0416. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftVertices_Definitions

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared19.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared19
end
