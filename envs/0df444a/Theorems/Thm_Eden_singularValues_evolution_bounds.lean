-- Prove2me | Theorems.Thm_Eden_singularValues_evolution_bounds
-- name    : Eden.singularValues_evolution_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:07.897338+00:00
-- url     : https://prove2.me/theorems/da18a8e2-1086-460a-94a7-0b191e9accb7
-- title:
--   Eden: singular Values evolution bounds
-- statement:
--   The Eden construction uses the singular Values evolution bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/IntegerGrowthBounds.lean#L65-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/IntegerGrowthBounds.lean#L65-L72

import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_IntegerGrowthBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValues_evolution_bounds {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 5) :
    Real.exp (-c * t) ≤ (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i ∧
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i ≤ Real.exp (3 * t) := by sorry
