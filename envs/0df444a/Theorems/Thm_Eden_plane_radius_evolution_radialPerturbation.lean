-- Prove2me | Theorems.Thm_Eden_plane_radius_evolution_radialPerturbation
-- name    : Eden.plane_radius_evolution_radialPerturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:30.244102+00:00
-- url     : https://prove2.me/theorems/f8dc9243-a020-4968-8cc9-6474597a97da
-- title:
--   Eden: plane radius evolution radial Perturbation
-- statement:
--   The Eden construction uses the plane radius evolution radial Perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L79-L89
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L79-L89

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.plane_radius_evolution_radialPerturbation (c : ℝ) (j : Fin 2)
    {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (s : ℝ) :
    ‖planeProjection j (evolution c t (radialPerturbation j r s))‖ = radiusEvolution t r := by sorry
