-- Prove2me | Theorems.Thm_Eden_norm_planeProjection_radialPerturbation
-- name    : Eden.norm_planeProjection_radialPerturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:44.380027+00:00
-- url     : https://prove2.me/theorems/c86794e6-4f8a-5b19-8435-0975a4fed721
-- title:
--   Eden: norm plane Projection radial Perturbation
-- statement:
--   The Eden construction uses the norm plane Projection radial Perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L60-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L60-L63

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.norm_planeProjection_radialPerturbation (j : Fin 2) (r s : ℝ) :
    ‖planeProjection j (radialPerturbation j r s)‖ = |r| := by sorry
