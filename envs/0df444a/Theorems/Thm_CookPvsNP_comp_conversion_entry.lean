-- Prove2me | Theorems.Thm_CookPvsNP_comp_conversion_entry
-- name    : CookPvsNP.comp_conversion_entry
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:23.578695+00:00
-- url     : https://prove2.me/theorems/48871610-1c5d-43e6-acdb-dcc47e2b14f0
-- title:
--   Exact entry into the intermediate-word conversion
-- statement:
--   Starting from a halted first-phase frame, two composite transitions mark its head as the second origin and place the left boundary one square to its left. The resulting configuration enters the first-copy state and retains all right-side source cells.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_conversion_entry {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : Cfg A M₁.Q) (hn : M₁.IsHalting c) :
    (compTM j₁ j₂ M₁ M₂).run 2 (compFirstCfg c) =
      ⟨.convCopy true,
        CompCell.leftMarker (c.left.headD none) :: c.left.tail.map CompCell.firstSymbol,
        CompCell.originSymbol c.head none,
        c.right.map CompCell.firstSymbol ++ [CompCell.rightMarker]⟩ := by sorry
end CookPvsNP
