-- Prove2me | Theorems.Thm_Eden_exists_complete_solution_in_attractor
-- name    : Eden.exists_complete_solution_in_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:29.523605+00:00
-- url     : https://prove2.me/theorems/d716ba7a-5917-5779-9e88-978e51b4c602
-- title:
--   Eden: exists complete solution in attractor
-- statement:
--   For every real `c`, every point of `A` lies on an ODE solution
--   defined for all real times and remaining in `A`.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L107-L111
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L107-L111

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exists_complete_solution_in_attractor (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧ ∀ t : ℝ,
      f t ∈ attractor ∧ HasDerivAt f (vectorField c (f t)) t := by sorry
