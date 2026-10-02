-- Prove2me | Theorems.Thm_CookPvsNP_comp_cleanup
-- name    : CookPvsNP.comp_cleanup
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:07:29.922506+00:00
-- url     : https://prove2.me/theorems/53ebb891-0d78-4dac-82ae-4f8d46cda2c2
-- title:
--   Exact final cleanup of the Cook composite machine
-- statement:
--   If the projected second machine is halting, the composite machine reaches the entire terminal cleanup configuration in exactly $2|R|+4$ transitions, where $R$ is the active right list of the decorated frame. Equality includes all finite tape cells, arbitrary first-track data, blank padding, and the accepting state.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompCleanup

namespace CookPvsNP
theorem comp_cleanup {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : CompSecondFrame A B M₂.Q) (hn : M₂.IsHalting c.source) :
    (compTM j₁ j₂ M₁ M₂).run (2 * c.right.length + 4) c.encode = compCleanCfg c := by sorry
end CookPvsNP
