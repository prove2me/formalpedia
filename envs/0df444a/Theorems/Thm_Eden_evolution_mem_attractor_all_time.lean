-- Prove2me | Theorems.Thm_Eden_evolution_mem_attractor_all_time
-- name    : Eden.evolution_mem_attractor_all_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:23.625843+00:00
-- url     : https://prove2.me/theorems/942a26f2-e453-4983-bfb5-a412337336a2
-- title:
--   Eden: evolution mem attractor all time
-- statement:
--   The Eden construction uses the evolution mem attractor all time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L94-L103
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L94-L103

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.evolution_mem_attractor_all_time (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    evolution c t p ∈ attractor := by sorry
