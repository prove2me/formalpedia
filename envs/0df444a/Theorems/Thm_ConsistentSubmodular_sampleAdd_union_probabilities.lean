-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleAdd_union_probabilities
-- name    : ConsistentSubmodular.sampleAdd_union_probabilities
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:11.849143+00:00
-- url     : https://prove2.me/theorems/a5eea833-345e-4dd0-b626-9b0bb7597e92
-- title:
--   Composing independent samples takes the union of inclusion probabilities
-- statement:
--   Let $U$ be a finite set, $p,q:\iota\to\mathbb{R}$, $v:2^\iota\to\mathbb{R}$ and $B\subseteq\iota$. Define the sampling operator
--   $$(\mathrm{Add}_U^{p}v)(B)=\sum_{S\subseteq U}\Big(\prod_{i\in S}p_i\prod_{i\in U\setminus S}(1-p_i)\Big)\,v(B\cup S).$$
--   Then for every $B$
--
--   $$\mathrm{Add}_U^{p}\big(\mathrm{Add}_U^{q}v\big)(B)\;=\;\mathrm{Add}_U^{\,p+q-pq}\,v\,(B),$$
--
--   where $(p+q-pq)_i=p_i+q_i-p_iq_i$. No range condition on $p,q$ is assumed.
--
--   Two independent samples of the same universe $U$ combine to one independent sample whose inclusion probabilities are $1-(1-p_i)(1-q_i)$. As the docstring notes, the identity is purely finite polynomial algebra.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/SamplingOperators.lean#L150-L166 (`ConsistentSubmodular.sampleAdd_union_probabilities`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleAdd_union_probabilities (U : Finset ι) (p q : ι → ℝ)
    (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (sampleAdd U q v) B =
      sampleAdd U (fun i => p i + q i - p i * q i) v B := by sorry
