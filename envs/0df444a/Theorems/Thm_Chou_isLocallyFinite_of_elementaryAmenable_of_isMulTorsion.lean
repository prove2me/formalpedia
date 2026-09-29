-- Prove2me | Theorems.Thm_Chou_isLocallyFinite_of_elementaryAmenable_of_isMulTorsion
-- name    : Chou.isLocallyFinite_of_elementaryAmenable_of_isMulTorsion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:54:22.942754+00:00
-- url     : https://prove2.me/theorems/ec631c35-fe12-443a-bd4e-e6f1822cd3e0
-- title:
--   Theorem 2.3: periodic elementary amenable groups are locally finite
-- statement:
--   If $G$ is elementary amenable and every element of $G$ has finite order, then every finitely
--   generated subgroup of $G$ is finite.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Theorem 2.3, first statement, p. 398

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Theorem 2.3, first statement: every periodic group in `EG` is locally finite. -/
theorem isLocallyFinite_of_elementaryAmenable_of_isMulTorsion {G : Type*} [Group G] (hG : ElementaryAmenable G) (ht : IsMulTorsion G) :
    IsLocallyFinite G := by
  sorry

end Chou
