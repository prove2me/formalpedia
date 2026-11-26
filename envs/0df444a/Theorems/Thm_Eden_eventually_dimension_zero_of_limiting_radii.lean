-- Prove2me | Theorems.Thm_Eden_eventually_dimension_zero_of_limiting_radii
-- name    : Eden.eventually_dimension_zero_of_limiting_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:20.072133+00:00
-- url     : https://prove2.me/theorems/db4122c4-c951-43f1-8396-463d42c6ac40
-- title:
--   Eden: eventually dimension zero of limiting radii
-- statement:
--   For `c > 4`, if both limiting squared radii vanish, all five normalized
--   singular-value logarithms are eventually negative and the finite-time
--   dimension is eventually exactly zero. This holds at every ambient point
--   satisfying the radius conditions, without an attractor assumption.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L78-L86
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L78-L86

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.eventually_dimension_zero_of_limiting_radii {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0) :
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by sorry
