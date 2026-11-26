-- Prove2me | Theorems.Thm_Eden_singularValueFunction_integer_evolution_bounds
-- name    : Eden.singularValueFunction_integer_evolution_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:38:03.399841+00:00
-- url     : https://prove2.me/theorems/08ecf394-de3b-4201-a445-681bf3234cb9
-- title:
--   Eden: singular Value Function integer evolution bounds
-- statement:
--   Explicit bounds on the nonnegative time domain, including t=0 and k=0.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/IntegerGrowthBounds.lean#L75-L93
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/IntegerGrowthBounds.lean#L75-L93

import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_IntegerGrowthBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_integer_evolution_bounds {k : ℕ} (hk : k ≤ 5)
    {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    Real.exp ((k : ℝ) * (-c * t)) ≤
        singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ∧
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ≤
        Real.exp ((k : ℝ) * (3 * t)) := by sorry
