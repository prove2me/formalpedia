-- Prove2me | Theorems.Thm_ConsistentSubmodular_randomizedLower
-- name    : ConsistentSubmodular.randomizedLower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:19.74921+00:00
-- url     : https://prove2.me/theorems/8e3393f6-4e36-46f1-bd9f-fe1b461b44d3
-- title:
--   Theorem 2 — randomized clairvoyant algorithm with ratio $\xi_\star-\varepsilon$ and $O(\varepsilon^{-2})$ recourse
-- statement:
--   There is an absolute constant $K$ such that for every $\varepsilon\in(0,1)$ there is an integer $C\le K\varepsilon^{-2}$ for which the following holds. For every stream length $n$, budget $k$ and nonnegative monotone submodular $f$ on $[n]$ there is a probability distribution $\mu$ over trajectories $(S_0,\dots,S_n)$ of a randomized clairvoyant algorithm such that:
--
--   1. every trajectory in the support of $\mu$ satisfies $S_0=\emptyset$, $S_t\subseteq X_t=\{x_1,\dots,x_t\}$, $|S_t|\le k$, and $|S_t\,\triangle\,S_{t-1}|\le C$ for all $t$;
--   2. for every time $t$ and every $A\subseteq X_t$ with $|A|\le k$,
--   $$(\xi_\star-\varepsilon)\,f(A)\ \le\ \mathbb E_\mu\, f(S_t).$$
--
--   The constant $C$ depends only on $\varepsilon$, not on $n$, $k$ or $f$.
--
--   Role: the lower-bound half of Main Result 1, obtained from Lemma 4, Lemma 3, Lemma 2 (with $\alpha=\xi_\star$) and Lemma 1 (with $\gamma=\min\{\varepsilon/3,1/16\}$).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L69-L79 (`ConsistentSubmodular.randomizedLower`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.randomizedLower : RandomizedLowerGoal := by sorry
