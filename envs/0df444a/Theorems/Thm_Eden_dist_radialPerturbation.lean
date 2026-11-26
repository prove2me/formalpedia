-- Prove2me | Theorems.Thm_Eden_dist_radialPerturbation
-- name    : Eden.dist_radialPerturbation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:27:13.968296+00:00
-- url     : https://prove2.me/theorems/b5b3772c-5ddd-594a-9883-6591943294b0
-- title:
--   Eden: dist radial Perturbation
-- statement:
--   The Eden construction uses the dist radial Perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L73-L77
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L73-L77

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.dist_radialPerturbation (j : Fin 2) (r u s : ℝ) :
    dist (radialPerturbation j r s) (radialPerturbation j u s) = |r - u| := by sorry
