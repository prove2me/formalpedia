-- Prove2me | Theorems.Thm_Eden_eventually_dimension_formula_zero_two
-- name    : Eden.eventually_dimension_formula_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:14:16.001618+00:00
-- url     : https://prove2.me/theorems/3a8c0cfd-e661-40a3-8ac2-70a4eed93e50
-- title:
--   Eden: eventually dimension formula zero two
-- statement:
--   The eventual quotient and all signs for the row with one neutral exponent,
--   allowing either order of the two planar radii.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L191-L218
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L191-L218

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.eventually_dimension_formula_zero_two {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧
        limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧
        limitingSquaredRadius (radiusSq₂ p) = 0)) :
    ∀ᶠ t in atTop, 0 ≤ normalizedLogSingularValues c t p 0 ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 2 < 0 ∧
      normalizedLogSingularValues c t p 1 < 0 ∧
      finiteTimeDimension c t p = 1 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 1 /
          -normalizedLogSingularValues c t p 1 := by sorry
