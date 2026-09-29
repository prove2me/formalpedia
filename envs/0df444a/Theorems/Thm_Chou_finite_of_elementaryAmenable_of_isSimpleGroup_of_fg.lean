-- Prove2me | Theorems.Thm_Chou_finite_of_elementaryAmenable_of_isSimpleGroup_of_fg
-- name    : Chou.finite_of_elementaryAmenable_of_isSimpleGroup_of_fg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:56:04.658981+00:00
-- url     : https://prove2.me/theorems/3d43137a-3dbd-431d-afb1-9028dc8017f9
-- title:
--   Corollary 2.4: a finitely generated simple group in $EG$ is finite
-- statement:
--   If $G$ is elementary amenable, finitely generated and simple, then $G$ is finite.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Corollary 2.4, p. 398

import Definitions.Def_Chou_ElementaryAmenable
import Mathlib

namespace Chou

/-- Corollary 2.4: a finitely generated simple group in `EG` is finite. -/
theorem finite_of_elementaryAmenable_of_isSimpleGroup_of_fg {G : Type*} [Group G] (hG : ElementaryAmenable G) [Group.FG G] [IsSimpleGroup G] :
    Finite G := by
  sorry

end Chou
