-- Prove2me | Theorems.Thm_CliffordHierTest_theorem_1_estimate
-- name    : CliffordHierTest.theorem_1_estimate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:31.015353+00:00
-- url     : https://prove2.me/theorems/33d1879d-177b-40f3-9eec-edf21fcb72a2
-- title:
--   Proof of Theorem 1 — the estimation step: $O(1/\varepsilon)$ queries via amplitude estimation
-- statement:
--   There is a constant $c$ such that for every prime $d$, every $n$ and every $0<\varepsilon\le0.04$ there is a query circuit $A$ with at most $c/\varepsilon$ queries to $U$ and $U^*$ and at most $c\,((n+1)(1+1/\varepsilon))^c$ gates such that for every $U\in\mathcal U(d^n)$:
--
--   1. if $\|U\|_{P^4}^{16}\ge1-16\varepsilon$, then $A$ outputs $1$ with probability at least $0.9$;
--   2. if $\|U\|_{P^4}^{16}\le1-18\varepsilon$, then $A$ outputs $0$ with probability at least $0.9$.
--
--   The source obtains this by estimating $\|U\|_{P^4}^{16}$ to additive error $\varepsilon$ with amplitude estimation on Algorithm 1.
--
--   Differences from the source:
--
--   - reading: distinguish the two cases by estimating ‖U‖¹⁶_{P⁴} up to additive error ε, with O(1/ε) queries by amplitude estimation → a Circuit (oracle gates for U and U* without control, elementary gates on ≤ 3 qudits, output wire 0) chosen before U, with queries ≤ c/ε, size ≤ c((n+1)(1+1/ε))^c, deciding the two cases with probability ≥ 0.9; reason: the source names no model of computation; this is the model of the goal theorem, and 0.9 is the success probability of Theorem 1
--   - encoding: ε ≤ 0.04 → ε ≤ 1/25; reason: 0.04 = 1/25
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §5 proof of Theorem 1, p.13 (with Algorithm 2's success probability 9/10, p.12)

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy
import Definitions.Def_CliffordHierTest_QueryCircuit

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Proof of Theorem 1, the estimation step** (p.13). Z. Bao, J. Briët, D. Castro-Silva,
P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and near-extremizers of noncommutative
uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
The two cases `‖U‖_{P⁴}^{16} ≥ 1 − 16ε` and `‖U‖_{P⁴}^{16} ≤ 1 − 18ε` can be distinguished with
probability at least `0.9` by an efficient query circuit making `O(1/ε)` queries to `U` and `U*`
(amplitude estimation on Algorithm 1).

**Formalization Note.** The circuit model is `Circuit` (oracle gates for `U` and `U*`, no controlled
oracle, elementary gates on at most three qudits, output on wire `0`). One constant `c` is chosen
before `d`, `n`, `ε`; the circuit is chosen after `(d, n, ε)` and before `U`. `O(1/ε)` queries is
`queries ≤ c/ε`; efficiency is `size ≤ c · ((n + 1)(1 + 1/ε))^c`. `0 < ε ≤ 0.04` as in the proof
(`0.04 = 1/25`). `d` prime (§2.1); every `n`. -/
theorem theorem_1_estimate : ∃ c : ℕ, ∀ (d : ℕ) [Fact (Nat.Prime d)] (n : ℕ) (ε : ℝ),
    0 < ε → ε ≤ 1 / 25 → ∃ A : Circuit d n,
      (A.queries : ℝ) ≤ c / ε ∧ (A.size : ℝ) ≤ c * (((n : ℝ) + 1) * (1 + 1 / ε)) ^ c ∧
      ∀ U : QuditUnitary d n,
        (1 - 16 * ε ≤ pauliNorm 4 (U : QuditOperator d n) ^ 16 →
          9 / 10 ≤ A.acceptProb (U : QuditOperator d n)) ∧
        (pauliNorm 4 (U : QuditOperator d n) ^ 16 ≤ 1 - 18 * ε →
          9 / 10 ≤ 1 - A.acceptProb (U : QuditOperator d n)) := by sorry

end CliffordHierTest
