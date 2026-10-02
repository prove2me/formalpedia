-- Prove2me | Theorems.Thm_CookPvsNP_comp_second_halt
-- name    : CookPvsNP.comp_second_halt
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T08:47:36.868678+00:00
-- url     : https://prove2.me/theorems/87b649cf-70cc-46cf-b7b4-f133a15f1dcd
-- title:
--   Bounded second-phase simulation through the second source halt
-- statement:
--   Suppose the second source machine $M_2$ halts by time $n$ from the projection of a decorated frame $D$. There are $m\le n$ and a decorated frame $D'$ such that
--
--   $$C^{3m}(E_2(D))=E_2(D'),\qquad \pi(D')=M_2^n(\pi(D)).$$
--
--   Moreover, the length of the active right list in $D'$ is at most its original length plus $n$. The equality includes all administrative data. The length estimate supplies a linear bound for the following cleanup scan; it does not assume the old first-track data has been erased.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompSecondFrame

namespace CookPvsNP
theorem comp_second_halt {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M₂.Q) (n : ℕ)
    (hn : M₂.IsHalting (M₂.run n c.source)) :
    ∃ m ≤ n, ∃ d : CompSecondFrame Γ₁ Γ₂ M₂.Q,
      (compTM j₁ j₂ M₁ M₂).run (3 * m) c.encode = d.encode ∧
      d.source = M₂.run n c.source ∧ d.right.length ≤ c.right.length + n := by sorry
end CookPvsNP
