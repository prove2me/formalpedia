-- Prove2me | Theorems.Thm_CliffordHierTest_theorem_2
-- name    : CliffordHierTest.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:08.903502+00:00
-- url     : https://prove2.me/theorems/41c45ff8-54e0-4663-aab5-846516ffe2f7
-- title:
--   Theorem 2 — 99% inverse theorem for the $P^4$ norm
-- statement:
--   There is a constant $L>1$ such that for every prime $d$, every $n\ge1$ and every $U\in\mathcal U(d^n)$,
--   $$\max_{V\in\mathcal C^{(3)}}|\langle V,U\rangle|^2\ge1-L\big(1-\|U\|_{P^4}\big).$$
--
--   This is the paper's main technical contribution: unitaries with $P^4$ norm close to $1$ are close to the third level of the Clifford hierarchy, with a linear loss and a constant independent of $d$ and $n$.
--
--   Differences from the source:
--
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §1.1 Theorem 2, p.3; L = 16 max{C₄, 1/ε₄}, p.11

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Theorem 2** (99% inverse theorem for the `P⁴` norm) (p.3). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
There is a constant `L > 1` such that for every prime `d`, every `n ≥ 1` and every
`U ∈ 𝒰(dⁿ)`, `max_{V ∈ 𝒞^{(3)}} |⟨V, U⟩|² ≥ 1 − L(1 − ‖U‖_{P⁴})`.

**Formalization Note.** `L` is chosen before `d` and `n`, as printed. The left side is the
degree-3 Clifford fidelity `ℱ_{𝒞^{(3)}}(U)` of (1). -/
theorem theorem_2 : ∃ L : ℝ, 1 < L ∧ ∀ (d : ℕ) [Fact (Nat.Prime d)] (n : ℕ), 1 ≤ n →
    ∀ U : QuditUnitary d n,
      1 - L * (1 - pauliNorm 4 (U : QuditOperator d n)) ≤ cliffordFid 3 (U : QuditOperator d n) := by sorry

end CliffordHierTest
