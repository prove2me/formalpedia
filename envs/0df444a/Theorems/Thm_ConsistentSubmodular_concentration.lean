-- Prove2me | Theorems.Thm_ConsistentSubmodular_concentration
-- name    : ConsistentSubmodular.concentration
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:36.297487+00:00
-- url     : https://prove2.me/theorems/e5cfeb62-e6a6-4952-be4a-ca2437493925
-- title:
--   Lemma B.7 — the concentration bounds
-- statement:
--   Two bounds for random sets with independent coordinates.
--
--   1. (Lower tail for submodular functions) Let $G$ be a nonnegative monotone submodular function on subsets of $[d]$ with all marginal values bounded, $G(A\cup\{e\})-G(A)\le c$ for all $A$ and $e$, where $c>0$. Let $S\subseteq[d]$ contain each $i$ independently with probability $q_i\in[0,1]$ and let $\mu=\mathbb E\,G(S)$. Then for every $a$ with $0<a<\mu$,
--   $$\Pr\{G(S)\le\mu-a\}\ \le\ \exp\!\Big(-\frac{a^2}{2c\mu}\Big).$$
--   2. (Upper tail for cardinality) Let $q_i\in[0,1]$ with $\sum_iq_i\le\kappa$, let $S$ contain each $i$ independently with probability $q_i$, and let $X=|S|$. Then for every $\eta\in(0,1]$,
--   $$\Pr\{X>(1+\eta)\kappa\}\ \le\ \exp\!\Big(-\frac{\eta^2\kappa}{3}\Big).$$
--
--   Role: Appendix B.2.3, bounds (37) and (38); used when rounding fractional windows to integral sets with high probability.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L154-L156 (`ConsistentSubmodular.concentration`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.concentration : ConcentrationGoal := by sorry
