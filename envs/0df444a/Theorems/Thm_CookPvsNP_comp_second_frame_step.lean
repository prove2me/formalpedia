-- Prove2me | Theorems.Thm_CookPvsNP_comp_second_frame_step
-- name    : CookPvsNP.comp_second_frame_step
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T08:47:10.614835+00:00
-- url     : https://prove2.me/theorems/f6f52f72-ae79-4f86-892d-988388c6f6ff
-- title:
--   Exact finite-configuration simulation of a second-machine step
-- statement:
--   Let $D$ be a decorated second-phase configuration, $\pi(D)$ its source-machine projection, $E_2(D)$ its composite-machine encoding, and $U(D)$ the administrative frame update. Then
--
--   $$\pi(U(D))=M_2(\pi(D)).$$
--
--   If the projected configuration is nonhalting, the existing composite machine $C$ satisfies
--
--   $$C^3(E_2(D))=E_2(U(D)).$$
--
--   This includes both boundary-extension cases, arbitrary old first-track data, and any explicit blank padding beyond the right marker.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompSecondFrame

namespace CookPvsNP
theorem comp_second_frame_step {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M₂.Q) :
    (c.step M₂).source = M₂.step c.source ∧
    (¬ M₂.IsHalting c.source →
      (compTM j₁ j₂ M₁ M₂).run 3 c.encode = (c.step M₂).encode) := by sorry
end CookPvsNP
