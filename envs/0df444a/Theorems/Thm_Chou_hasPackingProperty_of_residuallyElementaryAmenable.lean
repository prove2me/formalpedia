-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_residuallyElementaryAmenable
-- name    : Chou.hasPackingProperty_of_residuallyElementaryAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:05:43.626473+00:00
-- url     : https://prove2.me/theorems/cfc7140d-d34b-494a-a50b-ea30c2b70127
-- title:
--   Corollary 4.7: residually elementary amenable groups have property (P)
-- statement:
--   If for every $x \ne 1$ in $G$ there is a normal subgroup $K$ with $x \notin K$ and $G/K$
--   elementary amenable, then $G$ has property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Corollary 4.7, pp. 405–406

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Corollary 4.7: a group which is residually in `EG` has property (P). -/
theorem hasPackingProperty_of_residuallyElementaryAmenable {G : Type*} [Group G]
    (h : ResiduallyElementaryAmenable G) : HasPackingProperty G := by
  sorry

end Chou
