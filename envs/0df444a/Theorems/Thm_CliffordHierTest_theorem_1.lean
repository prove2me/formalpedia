-- Prove2me | Theorems.Thm_CliffordHierTest_theorem_1
-- name    : CliffordHierTest.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:21.806707+00:00
-- url     : https://prove2.me/theorems/ddc82c49-0f3d-48fb-b2e9-1da4c148b04d
-- title:
--   Theorem 1 — tolerant tester for $\mathcal C^{(3)}$ with $O(1/\varepsilon)$ queries to $U$ and $U^*$
-- statement:
--   There exist constants $C>1$ and $c$ such that the following holds for every prime $d$, every $n$ and every $\varepsilon>0$. There is a query circuit $A$ making at most $c/\varepsilon$ queries to $U$ and $U^*$ and having at most $c\,((n+1)(1+1/\varepsilon))^c$ gates such that for every unitary $U\in\mathcal U(d^n)$:
--
--   1. if $\mathcal F_{\mathcal C^{(3)}}(U)\ge1-\varepsilon$, then $A$ outputs $1$ with probability at least $0.9$;
--   2. if $\mathcal F_{\mathcal C^{(3)}}(U)\le1-C\varepsilon$, then $A$ outputs $0$ with probability at least $0.9$.
--
--   Here $\mathcal F_{\mathcal C^{(3)}}(U)=\max_{V\in\mathcal C^{(3)}}|\langle V,U\rangle|^2$ is the degree-3 Clifford fidelity. This is the paper's main result: an efficient tolerant tester for the third level of the Clifford hierarchy, the first level beyond the Clifford group, using $O(1/\varepsilon)$ queries.
--
--   **Formalization Note** The circuit is fixed after $(d,n,\varepsilon)$ and before $U$, and touches $U$ only through uncontrolled oracle gates for $U$ and $U^*$; the constants $C$ and $c$ do not depend on $d$, $n$ or $\varepsilon$.
--
--   Differences from the source:
--
--   - reading: query access to U and U*, an efficient algorithm C3Tester(n, d, U, U*, ε) → a Circuit: qudit wires, uncontrolled oracle gates for U and U*, elementary gates on at most three qudits, one final measurement of wire 0, chosen after (d, n, ε) and before U; reason: the source names no model of computation; this is the standard query model with the access the source grants
--   - reading: efficient → size ≤ c((n+1)(1+1/ε))^c with one constant c chosen before d, n, ε; reason: polynomial in n and 1/ε, uniform in d; the (1+1/ε) form allows a one-gate circuit for large ε
--   - reading: O(1/ε) queries to U and U* → queries ≤ c/ε, queries to U and U* counted together, c chosen before d, n, ε; reason: the meaning of O(1/ε) uniform in n, d, U
--   - reading: d (Theorem 1 does not restate it) → d prime; reason: standing assumption of §2.1, p.4
--   - generalization: n (Theorem 2, used in the proof, needs n ≥ 1) → every n, including n = 0; reason: at n = 0 every unitary is a phase and ℱ = 1, so only the first case occurs; the statement specializes to the source's
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §1.1 Theorem 1, p.2; proof, p.13

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy
import Definitions.Def_CliffordHierTest_QueryCircuit

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Theorem 1** (tolerant tester for `𝒞^{(3)}`) (p.2). Z. Bao, J. Briët, D. Castro-Silva,
P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and near-extremizers of noncommutative
uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
There is a constant `C > 1` such that, given `ε > 0` and query access to a unitary `U ∈ 𝒰(dⁿ)` and
its inverse `U*`, there is an efficient algorithm making `O(1/ε)` queries to `U` and `U*` that,
with probability at least `0.9`, outputs `1` if `ℱ_{𝒞^{(3)}}(U) ≥ 1 − ε` and outputs `0` if
`ℱ_{𝒞^{(3)}}(U) ≤ 1 − Cε`.

**Formalization Note.** `d` prime is the standing assumption of §2.1; every `n` (at `n = 0` every
`U` is a phase and only the first case occurs). The algorithm is a `Circuit` (qudit wires, oracle
gates for `U` and `U*` without control, elementary gates on at most three qudits, one final
measurement of wire `0`), chosen after `(d, n, ε)` and before `U`. The constants `C` and `c` are
chosen before `d`, `n`, `ε`: `O(1/ε)` queries is `queries ≤ c/ε` (queries to `U` and `U*` counted
together), and "efficient" is `size ≤ c · ((n + 1)(1 + 1/ε))^c`, a bound uniform in `d`. The
fidelity `ℱ_{𝒞^{(3)}}` is the supremum of `|⟨V, U⟩|²` over `𝒞^{(3)}`. -/
theorem theorem_1 : ∃ C : ℝ, 1 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) [Fact (Nat.Prime d)] (n : ℕ) (ε : ℝ),
    0 < ε → ∃ A : Circuit d n,
      (A.queries : ℝ) ≤ c / ε ∧ (A.size : ℝ) ≤ c * (((n : ℝ) + 1) * (1 + 1 / ε)) ^ c ∧
      ∀ U : QuditUnitary d n,
        (1 - ε ≤ cliffordFid 3 (U : QuditOperator d n) →
          9 / 10 ≤ A.acceptProb (U : QuditOperator d n)) ∧
        (cliffordFid 3 (U : QuditOperator d n) ≤ 1 - C * ε →
          9 / 10 ≤ 1 - A.acceptProb (U : QuditOperator d n)) := by sorry

end CliffordHierTest
