-- Prove2me | Theorems.Thm_Eden_one_sub_plane_radius_le_infDist
-- name    : Eden.one_sub_plane_radius_le_infDist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:27:14.294591+00:00
-- url     : https://prove2.me/theorems/a3ef5420-bd61-51ec-a2d1-0a5d305a61e7
-- title:
--   Eden: one sub plane radius le inf Dist
-- statement:
--   The Eden construction uses the one sub plane radius le inf Dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L49-L54
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L49-L54

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.one_sub_plane_radius_le_infDist (j : Fin 2) {K : Set PhaseSpace}
    (hK : K.Nonempty) (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1)
    (p : PhaseSpace) : 1 - ‖planeProjection j p‖ ≤ Metric.infDist p K := by sorry
