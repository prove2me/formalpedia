-- Prove2me | Theorems.Thm_ConsistentSubmodular_consecutiveIntervalGap
-- name    : ConsistentSubmodular.consecutiveIntervalGap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:09.011844+00:00
-- url     : https://prove2.me/theorems/1367d376-4236-4051-86e5-31ff368fdbc5
-- title:
--   Lemma 4 — adaptivity gap of consecutive intervals is at least $\xi_\star$, tight for three intervals
-- statement:
--   Let $\xi_\star$ be the root of $\Psi(\xi)=89\xi^4-44\xi^3-19\xi^2-3\xi+1$ in $(1/2,1)$. The statement has two parts.
--
--   1. Every interval-selection instance $(\ell,r,p)$ (any $N$) with nonincreasing consecutive intervals and equalizing distribution $p$ satisfies $\Gamma(\ell,r,p)\ge\xi_\star$.
--   2. There exist reals $u_1,u_2$ with $0<u_1<1$, $\Phi(u_1)=0$ where $\Phi(x)=x^4+x^3-2x^2-3x+2$, such that $u_1$ is the only root of $\Phi$ in $(0,1)$, $u_2=u_1^2(1+u_1)$, and a three-interval instance ($N=2$) which is nonincreasing consecutive with equalizing distribution, has $\Gamma(\ell,r,p)=\xi_\star$, and has
--   $$\ell=(0,\,1,\,1+u_1),\quad r=(1,\,1+u_1,\,1+u_1+u_2),\quad p=\Big(u_2,\ \tfrac{u_2}{u_1}-u_2,\ 1-\tfrac{u_2}{u_1}\Big).$$
--
--   Role: Appendix A.6; the lower bound, together with Lemmas 2 and 3, gives the randomized algorithm, and the three-interval instance shows that $\xi_\star$ cannot be improved by this approach.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L63-L67 (`ConsistentSubmodular.consecutiveIntervalGap`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.consecutiveIntervalGap : ConsecutiveIntervalGapGoal := by sorry
