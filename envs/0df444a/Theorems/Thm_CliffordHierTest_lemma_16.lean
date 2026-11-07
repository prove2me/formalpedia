-- Prove2me | Theorems.Thm_CliffordHierTest_lemma_16
-- name    : CliffordHierTest.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:05.243065+00:00
-- url     : https://prove2.me/theorems/73d9c1ab-c774-43f5-a449-701747c6c84b
-- title:
--   Lemma 16 — $\|U\|_{P^2}^4=\sum_a|\hat U(a)|^4$
-- statement:
--   For every $U\in L(d^n)$ ($d$ prime),
--   $$\|U\|_{P^2}^4=\sum_{a\in\mathbb F_d^{2n}}|\hat U(a)|^4,\qquad \hat U(a)=\langle W_a,U\rangle.$$
--
--   The $P^2$ norm is the $L^4$ norm of the Fourier transform, the noncommutative counterpart of the classical $U^2$ identity.
--
--   Differences from the source: none.
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §3 Lemma 16 (with Definition 15), p.7

import Mathlib
import Definitions.Def_CliffordHierTest_PauliNorm

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Lemma 16** (p.7), with Definition 15. Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For every `U ∈ L(dⁿ)`, `‖U‖_{P²}⁴ = Σ_{a ∈ 𝔽_d^{2n}} |Û(a)|⁴`, where `Û(a) = ⟨W_a, U⟩`.

**Formalization Note.** Every matrix, not only unitaries, as printed. `d` prime (§2.1). -/
theorem lemma_16 (d n : ℕ) [Fact (Nat.Prime d)] (U : QuditOperator d n) :
    pauliNorm 2 U ^ 4 = ∑ a : DiscretePhaseSpace d n, ‖fourierCoeff U a‖ ^ 4 := by sorry

end CliffordHierTest
