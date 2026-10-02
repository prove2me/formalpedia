-- Prove2me | Theorems.Thm_CookPvsNP_comp_conversion_seek
-- name    : CookPvsNP.comp_conversion_seek
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:32.434916+00:00
-- url     : https://prove2.me/theorems/cb273870-0a0f-4832-a906-f239f6971bbd
-- title:
--   Exact scan to the previous right boundary
-- statement:
--   In its seek state, the composite machine crosses $n$ blank cells and erases the old right boundary in $n+1$ transitions. It then starts returning left with one explicit blank stored on its right. This is an equality of complete finite configurations.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_conversion_seek {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (n : ℕ) (left : List (Option (CompCell A B))) :
    (compTM j₁ j₂ M₁ M₂).run (n + 1)
      ⟨.convSeekOldRight, left,
        (List.replicate n none ++ [CompCell.rightMarker]).headD none,
        (List.replicate n none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.convReturn, (List.replicate n none ++ left).tail,
        (List.replicate n none ++ left).headD none, [none]⟩ := by sorry
end CookPvsNP
