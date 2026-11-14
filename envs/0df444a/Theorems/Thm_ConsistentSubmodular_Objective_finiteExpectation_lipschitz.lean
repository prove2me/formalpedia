-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_finiteExpectation_lipschitz
-- name    : ConsistentSubmodular.Objective.finiteExpectation_lipschitz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:38.251317+00:00
-- url     : https://prove2.me/theorems/0ced26cc-3a7b-4a96-b442-3fcea619169d
-- title:
--   Type-Lipschitz bound for the independent-sampling expectation
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$ and let $V\ge 0$ satisfy $f(\{i\})-f(\emptyset)\le V$ for every $i$. For type vectors $p,q\in[0,1]^n$, let $\mathbb E_p[f]$ denote $\mathbb E[f(S)]$ for the random set $S$ containing each $i$ independently with probability $p_i$. Then
--   $$\bigl|\,\mathbb E_p[f]-\mathbb E_q[f]\,\bigr|\;\le\;V\sum_{i=1}^{n}|p_i-q_i| .$$
--
--   The expectation is therefore $V$-Lipschitz in the $\ell_1$ distance of the type vectors, with $V$ a bound on singleton marginals. The proof couples the two samples through shared thresholds, whose expected number of changed coordinates is exactly the type $\ell_1$ distance. The estimate is used to move along a path of type vectors while controlling the loss of value.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/TypeLipschitz.lean#L52-L92 (`ConsistentSubmodular.Objective.finiteExpectation_lipschitz`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.finiteExpectation_lipschitz (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ i, f.value {i} - f.value ∅ ≤ V)
    (p q : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    |finiteExpectation p f.value - finiteExpectation q f.value| ≤
      V * ∑ i, |p i - q i| := by sorry
