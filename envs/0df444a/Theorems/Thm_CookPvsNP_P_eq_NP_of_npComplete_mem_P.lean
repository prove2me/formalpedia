-- Prove2me | Theorems.Thm_CookPvsNP_P_eq_NP_of_npComplete_mem_P
-- name    : CookPvsNP.P_eq_NP_of_npComplete_mem_P
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T13:56:45.822459+00:00
-- url     : https://prove2.me/theorems/49024fa3-3719-4b8a-ade8-48a57ec473e2
-- title:
--   Proposition 1(c): an NP-complete language in P gives P = NP
-- statement:
--   Let $\Sigma$ be a finite alphabet and $L\subseteq\Sigma^*$. If $L$ is NP-complete and $L\in\mathrm P_\Sigma$, then for every finite nonempty alphabet $\Sigma'$,
--   $$\mathrm P_{\Sigma'}=\mathrm{NP}_{\Sigma'}.$$
--
--   So a polynomial-time algorithm for a single NP-complete problem would settle the P versus NP problem in the positive, over every alphabet.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, p. 5, Proposition 1(c)

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Cook, Proposition 1(c): if some NP-complete language is in `P`, then `P = NP` (over every
finite nonempty alphabet). -/
theorem P_eq_NP_of_npComplete_mem_P {Sym : Type} [Fintype Sym] (L : Lang Sym)
    (hL : NPComplete L) (hP : L ∈ P Sym) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'], P Sym' = NP Sym' := by sorry

end CookPvsNP
