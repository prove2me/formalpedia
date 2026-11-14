-- Prove2me | Theorems.Thm_ConsistentSubmodular_deterministicTight
-- name    : ConsistentSubmodular.deterministicTight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:31.320951+00:00
-- url     : https://prove2.me/theorems/7ce86285-2b52-4cd9-b3b1-6bd46719baf4
-- title:
--   Main Result 2 — tight deterministic bound $3/4$ (Theorems 3 and 4)
-- statement:
--   Two statements hold simultaneously.
--
--   1. (Algorithm, Theorem 4) There is an absolute $K$ such that for every $\varepsilon\in(0,1)$ there is $R\le K\varepsilon^{-3}\log(1/\varepsilon)$ such that for every $n,k$ and nonnegative monotone submodular $f$ on $[n]$ there is a trajectory with $S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$, $|S_t\triangle S_{t-1}|\le R$ and $(\tfrac34-\varepsilon)f(A)\le f(S_t)$ for every $t$ and every $A\subseteq X_t$, $|A|\le k$.
--   2. (Impossibility, constant recourse) For every $\alpha>3/4$ and every $C\in\mathbb N$ there are $n,k,u$ and an unweighted coverage stream $\mathrm{cover}:[n]\to2^{[u]}$ such that every trajectory with $S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$, $|S_t\triangle S_{t-1}|\le C$ has a time $t$ and a set $A\subseteq X_t$, $|A|\le k$, with $f(S_t)<\alpha f(A)$.
--
--   Role: the tight deterministic result, with optimal ratio $3/4$, even for coverage functions.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L125-L127 (`ConsistentSubmodular.deterministicTight`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.deterministicTight : DeterministicTightGoal := by sorry
