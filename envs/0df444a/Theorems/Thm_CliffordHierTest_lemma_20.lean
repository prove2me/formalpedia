-- Prove2me | Theorems.Thm_CliffordHierTest_lemma_20
-- name    : CliffordHierTest.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:49.089936+00:00
-- url     : https://prove2.me/theorems/b7d86e1c-c869-4488-bb21-b0aa7b5cb72f
-- title:
--   Lemma 20 — $\Pr[\mathrm{PNormBias}=1]=\tfrac12(1+\|U\|_{P^k}^{2^k})$
-- statement:
--   Let $d$ be prime, $k\ge1$ and $U\in\mathcal U(d^n)$. The probability that Algorithm 1, $\mathrm{PNormBias}(n,d,k,U,U^*)$, outputs $1$ is
--   $$\frac12\Big(1+\|U\|_{P^k}^{2^k}\Big).$$
--
--   Algorithm 1 thus turns the $P^k$ norm into the bias of a coin, which the tester estimates.
--
--   Differences from the source:
--
--   - reading: the probability that the randomized Algorithm 1 outputs 1 → the average over the k − 1 uniformly sampled directions of the swap-test acceptance probability on |Φ⟩ and (∂_{h_{k−1}}⋯∂_{h₁}U ⊗ I)|Φ⟩, the swap test's result 1 being the symmetric outcome; reason: this is the output law of the algorithm as printed; the oracle for ∂_hU is the matrix W_hUW_h*U*
--   - reading: natural number k → k ≥ 1; reason: Algorithm 1 terminates only from k ≥ 1 (its base case is k = 1)
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §5 Lemma 20, p.12

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy
import Definitions.Def_CliffordHierTest_PNormBias

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Lemma 20** (p.12). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On
Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms*,
arXiv:2605.26983 (held version, sha256 610d53a6…).
The probability that `PNormBias(n, d, k, U, U*)` (Algorithm 1) outputs `1` is
`½(1 + ‖U‖_{P^k}^{2^k})`.

**Formalization Note.** `k ≥ 1` (Algorithm 1 recurses down to `k = 1`) and `U` unitary (the input of
Algorithm 1). The output probability `pnormBiasProb k U` is the average over the `k − 1` uniformly
sampled directions of the swap-test acceptance probability on `|Φ⟩` and `(V ⊗ I)|Φ⟩`,
`V = ∂_{h_{k-1}} ⋯ ∂_{h₁} U`. `d` prime (§2.1). -/
theorem lemma_20 (d n : ℕ) [Fact (Nat.Prime d)] (k : ℕ) (hk : 1 ≤ k) (U : QuditUnitary d n) :
    pnormBiasProb k (U : QuditOperator d n) =
      (1 / 2 : ℝ) * (1 + pauliNorm k (U : QuditOperator d n) ^ (2 ^ k)) := by sorry

end CliffordHierTest
