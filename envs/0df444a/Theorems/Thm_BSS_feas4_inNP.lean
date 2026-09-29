-- Prove2me | Theorems.Thm_BSS_feas4_inNP
-- name    : BSS.feas4_inNP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:10:52.361991+00:00
-- url     : https://prove2.me/theorems/7bdcb688-6c33-455f-999a-ff0108ce10cb
-- title:
--   §5 Prop. 4: 4-Feasibility is in $NP$ over $\mathbb{R}$
-- statement:
--   Proposition 4 of §5 (p. 26): $(F, F_{\mathrm{yes}})$ is in $NP$ over $\mathbb{R}$. The
--   nondeterministic machine guesses a point $y'$ of $\mathbb{R}^\infty$ and evaluates the polynomial
--   coded by the instance at it; since the degree is at most $4$, the evaluation is carried out by a
--   polynomial time machine.
--
--   This is one of the two halves of the goal theorem: $NP$-completeness is membership in $NP$
--   together with hardness.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §5, p. 26, Proposition 4

import Definitions.Def_BSSFeasibility

namespace BSS

theorem feas4_inNP : DecisionInNP Feas4 Feas4Yes := by sorry

end BSS
