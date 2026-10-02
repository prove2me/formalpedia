-- Prove2me | Theorems.Thm_CookPvsNP_comp_handoff
-- name    : CookPvsNP.comp_handoff
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:11.512986+00:00
-- url     : https://prove2.me/theorems/b0ef3863-ac4a-46a0-b222-aae1626cbd81
-- title:
--   A halted first output initializes the second simulation
-- statement:
--   Given a halting first source configuration whose output is the encoded word $w$, there exists a decorated second-phase frame reached in $2|R|+6$ composite steps. Its projection is exactly the second machine's initial configuration on w under the second embedding, and its active right list is no longer than the first source right list. All finite administrative data are retained.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompConversion

namespace CookPvsNP
theorem comp_handoff {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : Cfg A M₁.Q) (w : List S) (hn : M₁.IsHalting c)
    (hout : M₁.output c = w.map (some ∘ j₁)) :
    ∃ d : CompSecondFrame A B M₂.Q,
      (compTM j₁ j₂ M₁ M₂).run (2 * c.right.length + 6) (compFirstCfg c) = d.encode ∧
      d.source = M₂.init (w.map j₂) ∧ d.right.length ≤ c.right.length := by sorry
end CookPvsNP
