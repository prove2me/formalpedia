-- Prove2me | Theorems.Thm_EdenVerified_p28_finiteTimeDimension_of_limiting_unit_radii
-- name    : EdenVerified.p28_finiteTimeDimension_of_limiting_unit_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:42:44.452653+00:00
-- url     : https://prove2.me/theorems/9b61d866-80d3-538d-9891-454c8286741a
-- title:
--   Eden Verified: p28 finite Time Dimension of limiting unit radii
-- statement:
--   The Eden Verified construction uses the p28 finite Time Dimension of limiting unit radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1201-L1207
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1201-L1207

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p28_finiteTimeDimension_of_limiting_unit_radii :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1),
    finiteTimeDimension c t p = targetDimension c := by sorry
