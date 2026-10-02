-- Prove2me | Theorems.Thm_CookPvsNP_comp_conversion_copy
-- name    : CookPvsNP.comp_conversion_copy
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:30.863197+00:00
-- url     : https://prove2.me/theorems/2ff60cac-29d2-4f05-ad67-45fd980f7450
-- title:
--   Linear scan translating the intermediate word
-- statement:
--   The conversion copy state translates an encoded list of nonblank intermediate symbols from the first embedding to the second in exactly the list length many transitions. It preserves first-track symbols and arbitrary tape contents on both sides of the word.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_conversion_copy {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B) (xs : List S)
    (left right : List (Option (CompCell A B))) :
    (compTM j₁ j₂ M₁ M₂).run xs.length
      ⟨.convCopy false, left,
        (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ right).headD none,
        (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ right).tail⟩ =
      ⟨.convCopy false,
        (xs.map (fun x => CompCell.plain (some (j₁ x)) (some (j₂ x)))).reverse ++ left,
        right.headD none, right.tail⟩ := by sorry
end CookPvsNP
