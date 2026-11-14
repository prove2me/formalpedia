-- Prove2me | Theorems.Thm_APFPaper1_Source_exists_subfamily_of_subset_map
-- name    : APFPaper1.Source.exists_subfamily_of_subset_map
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:47:20.790743+00:00
-- url     : https://prove2.me/theorems/05a7634b-6368-4cfd-acd7-5c963be44c33
-- title:
--   Under an equivalence of task types, every subfamily of a mapped finite family is the image of a subfamily of the original
-- statement:
--   Under an equivalence of task types, every subfamily of a mapped finite family is the image of a subfamily of the original.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source

theorem APFPaper1.Source.exists_subfamily_of_subset_map {D D' : Type*} (e : D' ≃ D) (T : Finset D') (S : Finset D)
    (h : S ⊆ T.map e.toEmbedding) : ∃ T' : Finset D', T' ⊆ T ∧ T'.map e.toEmbedding = S := by sorry
