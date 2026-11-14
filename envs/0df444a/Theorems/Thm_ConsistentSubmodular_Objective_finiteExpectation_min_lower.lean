-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_finiteExpectation_min_lower
-- name    : ConsistentSubmodular.Objective.finiteExpectation_min_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:38.510677+00:00
-- url     : https://prove2.me/theorems/3c429b3b-c814-4df6-84c4-43f0a9771806
-- title:
--   Taking the coordinatewise minimum with a nearby type vector loses at most $V\,\|p-q\|_1$
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$ and let $V\ge 0$ satisfy $f(\{i\})-f(\emptyset)\le V$ for every $i$. For type vectors $p,q\in[0,1]^n$ let $\mathbb E_p[f]$ be the expectation of $f(S)$ over the random set containing each $i$ independently with probability $p_i$. Then
--   $$\mathbb E_p[f]\;-\;V\sum_{i=1}^{n}|p_i-q_i|\;\le\;\mathbb E_{\min(p,q)}[f],$$
--   where $\min(p,q)_i=\min(p_i,q_i)$.
--
--   Replacing $p$ by its coordinatewise minimum with a nearby point $q$ thus loses at most the singleton cap $V$ times their $\ell_1$ distance. It is used when a type vector must be reduced to fit under another one (for instance to respect a cardinality or containment constraint) at controlled cost.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/TypeLipschitz.lean#L94-L115 (`ConsistentSubmodular.Objective.finiteExpectation_min_lower`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.finiteExpectation_min_lower (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ i, f.value {i} - f.value ∅ ≤ V)
    (p q : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    finiteExpectation p f.value - V * ∑ i, |p i - q i| ≤
      finiteExpectation (fun i => min (p i) (q i)) f.value := by sorry
