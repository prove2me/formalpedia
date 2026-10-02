-- Prove2me | Theorems.Thm_CookPvsNP_comp_conversion_boundary
-- name    : CookPvsNP.comp_conversion_boundary
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:43.752973+00:00
-- url     : https://prove2.me/theorems/2f772f93-dd80-4e5c-8c2d-a70f237d684c
-- title:
--   Relocate the right boundary and start the second machine
-- statement:
--   After copying an intermediate word, let $r$ be the number of copied cells between the head and marked origin, and let $p$ be the remaining blank padding. In $r+2p+3$ transitions, conversion places or preserves the new right boundary, erases the old one if necessary, returns to the origin, and starts the second machine. The result retains exactly the original padding beyond the new boundary, including the empty-word mode.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_conversion_boundary {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (xs : List (CompCell A B)) (hx : ∀ x ∈ xs, x.secondOrigin = false)
    (a : Option A) (b : Option B) (left : List (Option (CompCell A B)))
    (padding : ℕ) (empty : Bool) :
    (compTM j₁ j₂ M₁ M₂).run (xs.length + 2 * padding + 3)
      ⟨if empty then .convEmptyRight else .convCopy false,
        xs.map CompCell.pack ++ CompCell.originSymbol a b :: left,
        (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
        (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b,
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate padding none⟩ := by sorry
end CookPvsNP
