-- Prove2me | Theorems.Thm_Eden_hasDerivAt_evolution_of_mem_attractor
-- name    : Eden.hasDerivAt_evolution_of_mem_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:55.641724+00:00
-- url     : https://prove2.me/theorems/328cb413-643d-447a-94b2-d9d2a7e51256
-- title:
--   Eden: has Deriv At evolution of mem attractor
-- statement:
--   The Eden construction uses the has Deriv At evolution of mem attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L63-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L63-L80

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_evolution_of_mem_attractor (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor) :
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by sorry
