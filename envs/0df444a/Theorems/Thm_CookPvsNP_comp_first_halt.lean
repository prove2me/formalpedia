-- Prove2me | Theorems.Thm_CookPvsNP_comp_first_halt
-- name    : CookPvsNP.comp_first_halt
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T08:29:56.559529+00:00
-- url     : https://prove2.me/theorems/19bbaacc-4940-4d85-b159-02726a19a6c1
-- title:
--   Bounded first-phase simulation through the first source halt
-- statement:
--   Suppose $M_1$ has halted after at most $n$ steps from configuration $c$. Let $C$ be the published composite machine and $E_1$ its exact first-phase representation. There is an integer $m\le n$ such that
--
--   $$C^{3m}(E_1(c))=E_1(M_1^n(c)).$$
--
--   The simulated phase stops when the first source machine first halts. Its resulting configuration is exactly the one obtained at the declared source deadline, because later source steps fix a halting configuration. The composite machine has not yet entered its conversion phase.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompFrames

namespace CookPvsNP
theorem comp_first_halt {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (n : ℕ) (hn : M₁.IsHalting (M₁.run n c)) :
    ∃ m ≤ n, (compTM j₁ j₂ M₁ M₂).run (3 * m) (compFirstCfg c) =
      compFirstCfg (M₁.run n c) := by sorry
end CookPvsNP
