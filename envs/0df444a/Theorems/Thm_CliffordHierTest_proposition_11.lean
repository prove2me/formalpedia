-- Prove2me | Theorems.Thm_CliffordHierTest_proposition_11
-- name    : CliffordHierTest.proposition_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:09.090004+00:00
-- url     : https://prove2.me/theorems/063dd5cb-358a-48ed-b6d8-f33cf1ac78b7
-- title:
--   Proposition 11 — $\mathcal P^{(k)}=\mathcal C^{(k)}$ for $k\ge2$, and $\mathcal F_{\mathcal P^{(k)}}=\mathcal F_{\mathcal C^{(k)}}$
-- statement:
--   Let $d$ be prime.
--
--   1. For $k\ge2$, $\mathcal P^{(k)}=\mathcal C^{(k)}$.
--   2. $\mathcal P^{(0)}=U(1)\mathcal C^{(0)}$ and $\mathcal P^{(1)}=U(1)\mathcal C^{(1)}$: the sets of degree $0$ and $1$ differ only by global phases.
--   3. For every $k\ge0$ and $U\in\mathcal U(d^n)$,
--   $$\mathcal F_{\mathcal P^{(k)}}(U)=\max_{V\in\mathcal P^{(k)}}|\langle V,U\rangle|^2=\max_{V\in\mathcal C^{(k)}}|\langle V,U\rangle|^2=\mathcal F_{\mathcal C^{(k)}}(U).$$
--
--   This identifies the extremizers of the Pauli uniformity norms with the Clifford hierarchy.
--
--   Differences from the source:
--
--   - encoding: U(1)𝒞 → {e^{iθ}V : θ ∈ ℝ, V ∈ 𝒞}; reason: the unit circle is {e^{iθ}}
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.2.2 Proposition 11 and the display after it, p.6

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Proposition 11** and the display after it (p.6). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For `k ≥ 2`, `𝒫^{(k)} = 𝒞^{(k)}`; `𝒫^{(0)} = U(1)𝒞^{(0)}` and `𝒫^{(1)} = U(1)𝒞^{(1)}`; and for every
`k ≥ 0` and `U ∈ 𝒰(dⁿ)`, `ℱ_{𝒫^{(k)}}(U) = ℱ_{𝒞^{(k)}}(U)`.

**Formalization Note.** `U(1)𝒮` is the set of phase multiples `e^{iθ} V`, `θ ∈ ℝ`, `V ∈ 𝒮`. Both
fidelities are suprema of `|⟨V, U⟩|²` over the respective sets. `d` prime (§2.1). -/
theorem proposition_11 (d n : ℕ) [Fact (Nat.Prime d)] :
    (∀ k : ℕ, 2 ≤ k → pauliPoly d n k = cliffordLevel d n k) ∧
    (∀ U : QuditUnitary d n, U ∈ pauliPoly d n 0 ↔ ∃ θ : ℝ, ∃ V ∈ cliffordLevel d n 0,
      (U : QuditOperator d n) = Complex.exp (θ * Complex.I) • (V : QuditOperator d n)) ∧
    (∀ U : QuditUnitary d n, U ∈ pauliPoly d n 1 ↔ ∃ θ : ℝ, ∃ V ∈ cliffordLevel d n 1,
      (U : QuditOperator d n) = Complex.exp (θ * Complex.I) • (V : QuditOperator d n)) ∧
    (∀ (k : ℕ) (U : QuditUnitary d n),
      polyFid k (U : QuditOperator d n) = cliffordFid k (U : QuditOperator d n)) := by sorry

end CliffordHierTest
