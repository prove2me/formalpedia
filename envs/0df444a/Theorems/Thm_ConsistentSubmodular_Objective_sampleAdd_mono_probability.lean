-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_sampleAdd_mono_probability
-- name    : ConsistentSubmodular.Objective.sampleAdd_mono_probability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:33.012058+00:00
-- url     : https://prove2.me/theorems/4ca8a5cb-a4c9-41e9-b0aa-5d76f0c5b304
-- title:
--   Sampled value is monotone in the inclusion probabilities
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$, $U\subseteq[n]$, and let $p,q:[n]\to\mathbb{R}$ satisfy $0\le p_i\le1$, $0\le q_i\le1$ and $p_i\le q_i$ for every $i\in U$. Then for every $B\subseteq[n]$
--
--   $$\sum_{S\subseteq U}\Big(\prod_{i\in S}p_i\prod_{i\in U\setminus S}(1-p_i)\Big)f(B\cup S)\;\le\;\sum_{S\subseteq U}\Big(\prod_{i\in S}q_i\prod_{i\in U\setminus S}(1-q_i)\Big)f(B\cup S).$$
--
--   That is, $\mathbb{E}[f(B\cup S_p)]\le\mathbb{E}[f(B\cup S_q)]$ for the independent random subsets $S_p,S_q\subseteq U$ with inclusion probabilities $p,q$.
--
--   This monotonicity in the sampling probabilities is used to compare physical samples with larger or smaller inclusion probabilities.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalSampling.lean#L82-L101 (`ConsistentSubmodular.Objective.sampleAdd_mono_probability`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.sampleAdd_mono_probability (U : Finset (Fin n)) (p q : Fin n → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ U, p i ≤ q i) (B : Finset (Fin n)) :
    sampleAdd U p f.value B ≤ sampleAdd U q f.value B := by sorry
