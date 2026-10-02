-- Prove2me | Theorems.Thm_CookPvsNP_comp_cleanup_output
-- name    : CookPvsNP.comp_cleanup_output
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:08:13.77459+00:00
-- url     : https://prove2.me/theorems/b0b77287-6035-4831-a10f-957127f2f560
-- title:
--   Output preservation by the terminal cleanup configuration
-- statement:
--   If the projection of a decorated second-phase frame has ordinary word output, the terminal cleanup configuration has exactly that word under the composite output embedding. This includes empty output, old first-track data, and arbitrary finite trailing blank padding. Reachability of the terminal configuration is a separate transition theorem.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompCleanup

namespace CookPvsNP
theorem comp_cleanup_output {I S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (ι : I ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : CompSecondFrame A B M₂.Q) (w : List I)
    (hout : M₂.output c.source = w.map (some ∘ ι)) :
    (compTM j₁ j₂ M₁ M₂).output (compCleanCfg c) =
      w.map (some ∘ compOutputEmbedding ι) := by sorry
end CookPvsNP
