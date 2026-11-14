-- Prove2me | Theorems.Thm_ConsistentSubmodular_additionRobustReduction
-- name    : ConsistentSubmodular.additionRobustReduction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:50.2111+00:00
-- url     : https://prove2.me/theorems/9e23a69b-976a-4115-8d6e-0699b07d634e
-- title:
--   Lemma 1 — from clairvoyant addition robustness to consistency
-- statement:
--   Say that $\alpha$ is *admitted* if every instance of the clairvoyant addition-robust problem with one future element per stage admits an $\alpha$-addition-robust distribution: a probability distribution over sets $S\subseteq V_{\mathrm{now}}$ with $|S|\le\kappa$ such that $\mathbb E[f(S\cup R_j)]\ge\alpha f(O_j\cup R_j)$ at every stage $j$.
--
--   There is an absolute constant $K\in\mathbb R$ such that for every $\gamma\in(0,1/8)$ there is a consistency bound $C\in\mathbb N$ with $C\le K\gamma^{-2}$ such that, for every $\alpha\in[0,1]$ that is admitted, the following holds. For every stream length $n$, budget $k$ and nonnegative monotone submodular objective $f$ there is a randomized clairvoyant algorithm $\mu$ all of whose realizations are feasible with cardinality budget $k$ and change budget $C$, and such that for every time $t$ and every set $A\subseteq X_t$ with $|A|\le k$,
--   $$(\alpha-3\gamma)\,f(A)\le\mathbb E_\mu\bigl[f(\mathrm{ALG}_t)\bigr].$$
--
--   So addition robustness with ratio $\alpha$ yields an $O(\gamma^{-2})$-consistent randomized algorithm that is an $(\alpha-3\gamma)$-approximation. The consistency bound $C$ is chosen before $\alpha$ and does not depend on it. This is the reduction of Appendix A.3, used for Theorem 2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L44-L47 (`ConsistentSubmodular.additionRobustReduction`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.additionRobustReduction : AdditionRobustReductionGoal := by sorry
