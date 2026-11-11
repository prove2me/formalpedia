-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_2_5
-- name    : ArbLindbladLearn.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:35.212331+00:00
-- url     : https://prove2.me/theorems/228a9f09-1a57-4f24-b09d-101bcef89c90
-- title:
--   Lemma 2.5 — endpoint weight sum $W=(4q^2-1)/(3T)$
-- statement:
--   For $q\in\mathbb N_{>0}$, $K>0$ and the Chebyshev–Lobatto nodes on $[0,T]$ with $T=1/K$,
--   $$W=\sum_{j=1}^q|\ell_j'(0)|=\frac1T\Big(\frac{4q^2-1}3\Big)=O(q^2K).$$
--
--   The weight sum controls how node errors propagate to the endpoint derivative (node accuracy $\eta_0=\varepsilon/(6W)$ in Algorithm 2) and the support threshold $\alpha=\eta^2/(4W^2)$.
--
--   Differences from the source:
--   - reading: = O(q²K) → ≤ (4/3)·q²·K; reason: the explicit constant is the strongest form of the O-clause and follows from the equality
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 2.5, eq. (11), p.17

import Mathlib
import Definitions.Def_ArbLindbladLearn_lagDeriv0

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn



/-- Lemma 2.5 (Endpoint weight bound; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), eq. (11), p.17). For the
Chebyshev–Lobatto nodes on `[0, T]` with `T = 1/K`, the endpoint weights satisfy
`W = Σ_{j=1}^q |ℓ′_j(0)| = (1/T)((4q² − 1)/3) = O(q²K)`.

**Formalization Note** `q ∈ ℕ_{>0}` and `K > 0` (Lemma 2.4). The `O(q²K)` clause is stated with the
explicit constant `4/3`. -/
theorem lemma_2_5 (q : ℕ) (hq : 0 < q) (K : ℝ) (hK : 0 < K) :
    chebW q (1 / K) = 1 / (1 / K) * ((4 * (q : ℝ) ^ 2 - 1) / 3) ∧
      chebW q (1 / K) ≤ 4 / 3 * (q : ℝ) ^ 2 * K := by sorry

end ArbLindbladLearn
