-- Prove2me | Theorems.Thm_CookPvsNP_SAT_npComplete
-- name    : CookPvsNP.SAT_npComplete
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T14:14:12.218569+00:00
-- url     : https://prove2.me/theorems/5560bb00-56f0-4540-b04e-1976757975d4
-- title:
--   Cook's theorem: CNF-Satisfiability is NP-complete
-- statement:
--   The language $\mathrm{SAT}$ of (codes of) satisfiable propositional formulas in conjunctive normal form is NP-complete:
--   $$\mathrm{SAT}\text{ is NP-complete}.$$
--
--   Formulas use variables $x_0,x_1,\dots$ and are written over the four-letter alphabet $\{+,-,1,;\}$. A literal $x_i$ is written $+1^i$ and $\neg x_i$ is written $-1^i$; every clause is the concatenation of its literals followed by $;$. By Proposition 1(c), the goal $\mathrm P\neq\mathrm{NP}$ is equivalent to $\mathrm{SAT}\notin\mathrm P$.
--
--   **Formalization Note** This is the CNF form of Satisfiability, which Cook proved NP-complete in 1971. Variable indices are written in unary.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, pp. 4–5 ("The main results in [9] are that several natural problems, including Satisfiability and 3-SAT ... are NP-complete"); S. Cook, The complexity of theorem-proving procedures, STOC 1971

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Cook [9] (Cook §2): Satisfiability (in conjunctive normal form) is NP-complete. -/
theorem SAT_npComplete : NPComplete SAT := by sorry

end CookPvsNP
