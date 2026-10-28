-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared14_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared14.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:39.032729+00:00
-- url     : https://prove2.me/theorems/e17e2315-8a72-48e6-a773-e5898b0c65ce
-- title:
--   Pair Light Prepared14 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared14.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft14.lean, lines 12-14, SHA-256 10628cf5e42f18767c1415f9a8f0aad0342124c383f9d9d555127ce130b5992e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftVertices_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared14.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared14
end
