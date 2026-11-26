-- Prove2me | Theorems.Thm_Eden_eventually_dimension_formula_two_two
-- name    : Eden.eventually_dimension_formula_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:13:57.749809+00:00
-- url     : https://prove2.me/theorems/d28ef263-754a-5725-b5ff-bdc9dd9758cc
-- title:
--   Eden: eventually dimension formula two two
-- statement:
--   The eventual quotient and all signs for the row with two neutral exponents.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L221-L242
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L221-L242

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.eventually_dimension_formula_two_two {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < 2 → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 3 < 0 ∧
      normalizedLogSingularValues c t p 2 < 0 ∧
      finiteTimeDimension c t p = 2 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 2 /
          -normalizedLogSingularValues c t p 2 := by sorry
