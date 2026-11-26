-- Prove2me | Theorems.Thm_Eden_radialPerturbation_mem_attractor
-- name    : Eden.radialPerturbation_mem_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:06.742352+00:00
-- url     : https://prove2.me/theorems/5999323f-bbe9-5ae9-9b9e-24e2d980131a
-- title:
--   Eden: radial Perturbation mem attractor
-- statement:
--   The Eden construction uses the radial Perturbation mem attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L65-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L65-L71

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.radialPerturbation_mem_attractor (j : Fin 2) {r s : ℝ}
    (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) : radialPerturbation j r s ∈ attractor := by sorry
