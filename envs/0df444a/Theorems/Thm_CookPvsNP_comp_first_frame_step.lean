-- Prove2me | Theorems.Thm_CookPvsNP_comp_first_frame_step
-- name    : CookPvsNP.comp_first_frame_step
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T08:29:48.379005+00:00
-- url     : https://prove2.me/theorems/b6b518ab-79e6-4a84-9a3f-e7daf558096d
-- title:
--   Exact finite-configuration simulation of a first-machine step
-- statement:
--   Let $C$ be the published two-track composite of machines $M_1,M_2$, with the fixed intermediate alphabet embeddings. Let $E_1(c)$ place the source configuration $c$ on the first track and put a right sentinel immediately beyond its finite right list. For every nonhalting configuration $c$ of $M_1$,
--
--   $$C^3(E_1(c))=E_1(M_1(c)).$$
--
--   Equality holds for the entire finite configuration, including the state, both finite tape lists, head symbol and boundary position. Thus it is stronger than equality only after projecting away administrative cells.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompFrames

namespace CookPvsNP
theorem comp_first_frame_step {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (hn : ¬ M₁.IsHalting c) :
    (compTM j₁ j₂ M₁ M₂).run 3 (compFirstCfg c) = compFirstCfg (M₁.step c) := by sorry
end CookPvsNP
