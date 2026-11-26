-- Prove2me | Theorems.Thm_Eden_plane_radius_sub_le_dist
-- name    : Eden.plane_radius_sub_le_dist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:25:37.770769+00:00
-- url     : https://prove2.me/theorems/ce9dc99f-9731-5f17-ba3e-50424e918155
-- title:
--   Eden: plane radius sub le dist
-- statement:
--   The Eden construction uses the plane radius sub le dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L41-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L41-L47

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.plane_radius_sub_le_dist (j : Fin 2) (p q : PhaseSpace) :
    ‖planeProjection j q‖ - ‖planeProjection j p‖ ≤ dist p q := by sorry
