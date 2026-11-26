-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_of_limiting_unit_radii
-- name    : Eden.finiteTimeDimension_of_limiting_unit_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:48.5452+00:00
-- url     : https://prove2.me/theorems/27738da9-4eb7-5588-b035-114f43c03f35
-- title:
--   Eden: finite Time Dimension of limiting unit radii
-- statement:
--   The Eden construction uses the finite Time Dimension of limiting unit radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L180-L187
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L180-L187

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.finiteTimeDimension_of_limiting_unit_radii {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1) :
    finiteTimeDimension c t p = targetDimension c := by sorry
