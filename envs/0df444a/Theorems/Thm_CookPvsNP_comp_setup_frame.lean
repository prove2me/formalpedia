-- Prove2me | Theorems.Thm_CookPvsNP_comp_setup_frame
-- name    : CookPvsNP.comp_setup_frame
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T08:29:47.596181+00:00
-- url     : https://prove2.me/theorems/5b451634-901e-4574-bffa-551896efd354
-- title:
--   Exact initialization of the Cook composite machine
-- statement:
--   Let $C$ be the published composite of $M_1,M_2$, and embed an input word $w$ on the first track with all markers initially absent. Its setup phase takes exactly
--
--   $$2\max(|w|,1)+2$$
--
--   transitions and ends at $E_1(\operatorname{init}_{M_1}(w))$: the original input is restored under its initial head, the state is the first simulation state, and the right sentinel is immediately beyond the finite source right list. For the empty word the sentinel is one cell to the right of the head. The equality concerns the full finite configuration.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompFrames

namespace CookPvsNP
theorem comp_setup_frame {I S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (ι : I ↪ Γ₁) (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (w : List I) :
    (compTM j₁ j₂ M₁ M₂).run (2 * max w.length 1 + 2)
      ((compTM j₁ j₂ M₁ M₂).init (w.map (compInputEmbedding ι))) =
      compFirstCfg (M₁.init (w.map ι)) := by sorry
end CookPvsNP
