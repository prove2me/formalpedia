-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared36_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared36.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:25:08.272301+00:00
-- url     : https://prove2.me/theorems/7b107d02-a948-4da2-9371-6882773fb725
-- title:
--   Pair Light Prepared36 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared36.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft36.lean, lines 12-14, SHA-256 fcc74b2ada6ab2c30b6f237bc30ff4fab95ab80fe33464a3c6b0e713456aea31. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftVertices_Definitions

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared36.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared36
end
