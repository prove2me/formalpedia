-- Prove2me | Theorems.Thm_CookPvsNP_comp_conversion_return
-- name    : CookPvsNP.comp_conversion_return
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:40.562175+00:00
-- url     : https://prove2.me/theorems/89b6afe2-60d7-40fd-acbf-6b5a1a8a205c
-- title:
--   Exact return to the marked second origin
-- statement:
--   Across a list of cells with no second-origin marker, the conversion return phase takes the list length plus two steps to find the marked origin, clear its flag, and bounce into the initial state of the second machine. Canonical packed cells and a nonempty right suffix ensure equality of the full finite representation.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_conversion_return {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (xs : List (CompCell A B)) (hx : ∀ x ∈ xs, x.secondOrigin = false)
    (a : Option A) (b : Option B) (left : List (Option (CompCell A B)))
    (r : Option (CompCell A B)) (rs : List (Option (CompCell A B)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (compTM j₁ j₂ M₁ M₂).run (xs.length + 2)
      ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
        (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by sorry
end CookPvsNP
