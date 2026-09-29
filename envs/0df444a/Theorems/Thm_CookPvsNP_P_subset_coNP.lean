-- Prove2me | Theorems.Thm_CookPvsNP_P_subset_coNP
-- name    : CookPvsNP.P_subset_coNP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T13:49:13.725545+00:00
-- url     : https://prove2.me/theorems/eddde6d0-c662-4bbc-b93f-464048ef609d
-- title:
--   P $\subseteq$ coNP
-- statement:
--   For every finite alphabet $\Sigma$,
--   $$\mathrm P_\Sigma\subseteq\mathrm{coNP}_\Sigma,$$
--   where $\mathrm{coNP}_\Sigma$ is the set of languages whose complements are in $\mathrm{NP}_\Sigma$.
-- source:
--   Formal Conjectures (Google DeepMind), FormalConjectures/Millennium/PvsNP.lean, https://github.com/google-deepmind/formal-conjectures (theorem P_subset_coNP); cf. S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, p. 5 (coNP)

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- `P ⊆ coNP`. -/
theorem P_subset_coNP (Sym : Type) [Fintype Sym] : P Sym ⊆ coNP Sym := by sorry

end CookPvsNP
