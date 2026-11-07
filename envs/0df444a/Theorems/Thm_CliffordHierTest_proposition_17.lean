-- Prove2me | Theorems.Thm_CliffordHierTest_proposition_17
-- name    : CliffordHierTest.proposition_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:02.194872+00:00
-- url     : https://prove2.me/theorems/62f8fd3c-9113-42d5-b3d7-dd1fd3c38561
-- title:
--   Proposition 17 — inverse theorem for $P^2$: $\mathcal F_{\mathcal C^{(1)}}(U)\ge\|U\|_{P^2}^4$
-- statement:
--   For all $U\in\mathcal U(d^n)$ ($d$ prime),
--   $$\mathcal F_{\mathcal C^{(1)}}(U)\ge\|U\|_{P^2}^4.$$
--
--   Together with Proposition 13 it shows that $\mathcal F_{\mathcal C^{(1)}}$ and $\|\cdot\|_{P^2}$ are polynomially related; it is the base of the representation-theoretic step of Theorem 19.
--
--   Differences from the source:
--
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §3 Proposition 17, p.7

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Proposition 17** (inverse theorem for `P²`) (p.7). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For all `U ∈ 𝒰(dⁿ)`, `ℱ_{𝒞^{(1)}}(U) ≥ ‖U‖_{P²}⁴`.

**Formalization Note.** `d` prime (§2.1); every `n`. -/
theorem proposition_17 (d n : ℕ) [Fact (Nat.Prime d)] (U : QuditUnitary d n) :
    pauliNorm 2 (U : QuditOperator d n) ^ 4 ≤ cliffordFid 1 (U : QuditOperator d n) := by sorry

end CliffordHierTest
