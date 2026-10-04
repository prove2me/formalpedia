-- Prove2me | Theorems.Thm_CookPvsNP_coP_eq_P
-- name    : CookPvsNP.coP_eq_P
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T13:48:14.247753+00:00
-- url     : https://prove2.me/theorems/829f0972-1c0c-4443-8f42-28a837892038
-- title:
--   P is closed under complement
-- statement:
--   For every finite alphabet $\Sigma$, the languages whose complements lie in P are exactly the languages in P:
--   $$\{\,L\subseteq\Sigma^* : \Sigma^*\setminus L\in\mathrm P_\Sigma\,\}=\mathrm P_\Sigma.$$
--
--   With $\mathrm P\subseteq\mathrm{NP}$ this gives $\mathrm P\subseteq\mathrm{coNP}$, and it shows that $\mathrm{NP}\neq\mathrm{coNP}$ implies $\mathrm P\neq\mathrm{NP}$.
-- source:
--   Formal Conjectures (Google DeepMind), FormalConjectures/Millennium/PvsNP.lean, https://github.com/google-deepmind/formal-conjectures (theorem coP_eq_P); cf. S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, p. 5 (coNP)

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- The complements of the languages in `P` are exactly the languages in `P`. -/
theorem coP_eq_P (Sym : Type) [Fintype Sym] : { L : Lang Sym | Lᶜ ∈ P Sym } = P Sym := by sorry

end CookPvsNP
