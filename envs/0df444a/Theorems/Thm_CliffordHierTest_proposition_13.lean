-- Prove2me | Theorems.Thm_CliffordHierTest_proposition_13
-- name    : CliffordHierTest.proposition_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:53.430116+00:00
-- url     : https://prove2.me/theorems/1dc3ad95-8533-4bc7-b73b-22f581ca0715
-- title:
--   Proposition 13 — direct inequality $\mathcal F_{\mathcal C^{(k-1)}}(U)\le\|U\|_{P^k}$
-- statement:
--   For all $U\in\mathcal U(d^n)$ ($d$ prime) and $k\ge1$,
--   $$\mathcal F_{\mathcal C^{(k-1)}}(U)\le\|U\|_{P^k}.$$
--
--   This is Theorem 8 of Bu–Gu–Jaffe; the tester uses it at $k=4$ to show that unitaries close to $\mathcal C^{(3)}$ have $P^4$ norm close to $1$.
--
--   Differences from the source:
--
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.2.2 Proposition 13, p.6

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Proposition 13** (direct inequality, Theorem 8 of [BGJ25]) (p.6). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For all `U ∈ 𝒰(dⁿ)` and `k ≥ 1`, `ℱ_{𝒞^{(k-1)}}(U) ≤ ‖U‖_{P^k}`.

**Formalization Note.** `d` prime (§2.1); every `n`. -/
theorem proposition_13 (d n : ℕ) [Fact (Nat.Prime d)] (k : ℕ) (hk : 1 ≤ k) (U : QuditUnitary d n) :
    cliffordFid (k - 1) (U : QuditOperator d n) ≤ pauliNorm k (U : QuditOperator d n) := by sorry

end CliffordHierTest
