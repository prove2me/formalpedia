-- Prove2me | Theorems.Thm_CookPvsNP_P_subset_NP
-- name    : CookPvsNP.P_subset_NP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T13:44:01.922442+00:00
-- url     : https://prove2.me/theorems/9aec48d8-4507-4e84-beb3-66f6bba78f41
-- title:
--   P $\subseteq$ NP
-- statement:
--   For every finite alphabet $\Sigma$, every language decidable in polynomial time is in NP:
--   $$\mathrm P_\Sigma\subseteq\mathrm{NP}_\Sigma.$$
--
--   This is the easy inclusion. P versus NP asks whether it is strict.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §1, p. 2 ("It is trivial to show that P ⊆ NP")

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Cook §1: `P ⊆ NP`. -/
theorem P_subset_NP (Sym : Type) [Fintype Sym] : P Sym ⊆ NP Sym := by sorry

end CookPvsNP
