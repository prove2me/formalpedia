-- Prove2me | Theorems.Thm_CliffordHierTest_theorem_1_gap
-- name    : CliffordHierTest.theorem_1_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:30.968983+00:00
-- url     : https://prove2.me/theorems/9cd35a06-e895-4c95-8ae1-e90a3c1d6f55
-- title:
--   Proof of Theorem 1 — the norm gap: $\|U\|_{P^4}^{16}\ge1-16\varepsilon$ versus $\le1-18\varepsilon$
-- statement:
--   There is a constant $L>0$ (the constant of Theorem 2) such that for every prime $d$, every $n$, every $U\in\mathcal U(d^n)$ and every $0<\varepsilon\le0.04$:
--
--   1. if $\mathcal F_{\mathcal C^{(3)}}(U)\ge1-\varepsilon$, then $\|U\|_{P^4}^{16}\ge1-16\varepsilon$;
--   2. if $\mathcal F_{\mathcal C^{(3)}}(U)\le1-2L\varepsilon$, then $\|U\|_{P^4}^{16}\le1-18\varepsilon$.
--
--   The two cases of the tester thus give a gap of $2\varepsilon$ in $\|U\|_{P^4}^{16}$, which is what the estimation step resolves.
--
--   Differences from the source:
--
--   - reading: L the constant guaranteed by Theorem 2 → ∃ L > 0, chosen before d, n, U, ε; reason: the step holds for the constant of Theorem 2; the existential states it without assuming Theorem 2 as a hypothesis
--   - generalization: n ≥ 1 (through Theorem 2) → every n, including n = 0; reason: at n = 0 every unitary is a phase, ℱ = ‖U‖_{P⁴} = 1, and only the first case can occur
--   - encoding: ε ≤ 0.04 → ε ≤ 1/25; reason: 0.04 = 1/25
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §5 proof of Theorem 1, p.13

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Proof of Theorem 1, the norm gap** (p.13). Z. Bao, J. Briët, D. Castro-Silva,
P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and near-extremizers of noncommutative
uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
With `L` the constant of Theorem 2 and `0 < ε ≤ 0.04`: if `ℱ_{𝒞^{(3)}}(U) ≥ 1 − ε` then
`‖U‖_{P⁴}^{16} ≥ 1 − 16ε`, and if `ℱ_{𝒞^{(3)}}(U) ≤ 1 − 2Lε` then `‖U‖_{P⁴}^{16} ≤ 1 − 18ε`.

**Formalization Note.** "The constant guaranteed by Theorem 2" is the existential `L > 0`, chosen
before `d`, `n`, `U` and `ε`; the statement holds for every `n` (at `n = 0` both sides are trivial).
`0.04` is written `1/25`. `d` prime (§2.1). -/
theorem theorem_1_gap : ∃ L : ℝ, 0 < L ∧ ∀ (d : ℕ) [Fact (Nat.Prime d)] (n : ℕ)
    (U : QuditUnitary d n) (ε : ℝ), 0 < ε → ε ≤ 1 / 25 →
      (1 - ε ≤ cliffordFid 3 (U : QuditOperator d n) →
        1 - 16 * ε ≤ pauliNorm 4 (U : QuditOperator d n) ^ 16) ∧
      (cliffordFid 3 (U : QuditOperator d n) ≤ 1 - 2 * L * ε →
        pauliNorm 4 (U : QuditOperator d n) ^ 16 ≤ 1 - 18 * ε) := by sorry

end CliffordHierTest
