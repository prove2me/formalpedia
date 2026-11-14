-- Prove2me | Theorems.Thm_ConsistentSubmodular_randomizedTight
-- name    : ConsistentSubmodular.randomizedTight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:39.553584+00:00
-- url     : https://prove2.me/theorems/ea1a0c26-86bc-49e0-8282-ccc56a9f7b56
-- title:
--   Main Result 1 — tight randomized bound $\xi_\star$ (Theorems 1 and 2)
-- statement:
--   Two statements hold simultaneously.
--
--   1. (Algorithm, Theorem 2) There is an absolute $K$ such that for every $\varepsilon\in(0,1)$ there is $C\le K\varepsilon^{-2}$ such that for every $n,k$ and nonnegative monotone submodular $f$ on $[n]$ there is a distribution $\mu$ on trajectories, each realization starting at $\emptyset$, with $S_t\subseteq X_t$, $|S_t|\le k$ and $|S_t\triangle S_{t-1}|\le C$, and with $(\xi_\star-\varepsilon)f(A)\le\mathbb E_\mu f(S_t)$ for every time $t$ and every $A\subseteq X_t$, $|A|\le k$.
--   2. (Impossibility, constant recourse) For every $C\in\mathbb N$ and $\delta>0$ there is $k_0$ such that for every $k\ge k_0$ there is a finite unweighted coverage stream (sets $\mathrm{cover}(e)$ over a finite universe, $f(A)=|\bigcup_{e\in A}\mathrm{cover}(e)|$) such that every distribution $\mu$ over trajectories that are feasible with budget $k$ and recourse $C$ has a time $t$ and a competitor $A\subseteq X_t$, $|A|\le k$, with
--   $$\mathbb E_\mu f(S_t)\ <\ (\xi_\star+\delta)\,f(A).$$
--
--   Role: the tight randomized result, with $\xi_\star\approx0.7942$ the root of $\Psi$ in $(1/2,1)$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L81-L83 (`ConsistentSubmodular.randomizedTight`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.randomizedTight : RandomizedTightGoal := by sorry
