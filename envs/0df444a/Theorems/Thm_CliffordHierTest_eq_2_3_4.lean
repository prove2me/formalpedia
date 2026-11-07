-- Prove2me | Theorems.Thm_CliffordHierTest_eq_2_3_4
-- name    : CliffordHierTest.eq_2_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:01.886212+00:00
-- url     : https://prove2.me/theorems/71ffaff4-52d2-49be-ac1f-c878ad89a1b6
-- title:
--   (2)–(4) — basic properties and explicit forms of the Pauli uniformity norms
-- statement:
--   Let $d$ be prime. For all $k$ and all unitaries $U$,
--   $$\|U\|_{P^k}\le1. \tag{2}$$
--   For all matrices $U\in L(d^n)$ the norms satisfy the nesting property
--   $$\|U\|_{P^k}^{2^k}=\mathop{\mathbb E}_{h\in\mathbb F_d^{2n}}\|\partial_hU\|_{P^{k-1}}^{2^{k-1}}, \tag{3}$$
--   and the explicit forms
--   $$\|U\|_{P^1}^2=\frac1{d^{2n}}|\operatorname{tr}U|^2,\qquad \|U\|_{P^2}^4=\frac1{d^{2n}}\mathop{\mathbb E}_{h\in\mathbb F_d^{2n}}|\operatorname{tr}[\partial_hU]|^2. \tag{4}$$
--
--   (3) is stated for $k\ge2$, and also, for every $k\ge1$, for the averaged traces $\mathbb E_{h_1,\dots,h_k}d^{-n}\operatorname{tr}[\partial_{h_k}\cdots\partial_{h_1}U]$ before the root is taken. These identities drive the induction of Theorem 19 and the analysis of Algorithm 1.
--
--   Differences from the source:
--
--   - generalization: (2) for the P^k norms (k ≥ 1) → (2) for every k ∈ ℕ, including k = 0; reason: at k = 0 the expression is |d^{-n} tr U| ≤ 1; the statement specializes to the source's
--   - reading: (3) for the norms, all k → (3) for the norms for k ≥ 2, and for the averaged traces (the expression of Definition 8 before the root) for k ≥ 1; reason: at k = 1 the right side involves ‖·‖_{P⁰} = d^{-n} tr ∂_hU, a complex number, so the printed identity is read literally in the averaged-trace form
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.2.1 displays (2), (3), (4), p.5

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **(2), (3), (4)** (p.5). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
(2) `‖U‖_{P^k} ≤ 1` for unitary `U`; (3) `‖U‖_{P^k}^{2^k} = E_h ‖∂_h U‖_{P^{k-1}}^{2^{k-1}}`;
(4) `‖U‖_{P¹}² = d^{-2n} |tr U|²` and `‖U‖_{P²}⁴ = d^{-2n} E_h |tr ∂_h U|²` for every `U ∈ L(dⁿ)`.

**Formalization Note.** (2) is stated for every `k`, including `k = 0`. (3) is stated in two forms:
for the norms, for every `k ≥ 2` and every matrix; and for the averaged traces `pauliMoment`
(the expression of Definition 8 before the root), for every `k ≥ 1`. At `k = 1` the right side
of (3) involves `‖·‖_{P⁰}`, which is the complex number `d^{-n} tr ∂_h U`, not a norm; the
moment form is the printed identity read literally. `E_h` is the average over the
`d^{2n}` points of `𝔽_d^{2n}`. `d` prime is the standing assumption of §2.1. -/
theorem eq_2_3_4 (d n : ℕ) [Fact (Nat.Prime d)] :
    (∀ (k : ℕ) (U : QuditUnitary d n), pauliNorm k (U : QuditOperator d n) ≤ 1) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ U : QuditOperator d n,
      pauliNorm k U ^ (2 ^ k) = ((Fintype.card (DiscretePhaseSpace d n) : ℝ))⁻¹ *
        ∑ h : DiscretePhaseSpace d n, pauliNorm (k - 1) (pauliDeriv h U) ^ (2 ^ (k - 1))) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ U : QuditOperator d n,
      pauliMoment k U = ((Fintype.card (DiscretePhaseSpace d n) : ℂ))⁻¹ *
        ∑ h : DiscretePhaseSpace d n, pauliMoment (k - 1) (pauliDeriv h U)) ∧
    (∀ U : QuditOperator d n,
      pauliNorm 1 U ^ 2 = ((d : ℝ) ^ (2 * n))⁻¹ * ‖U.trace‖ ^ 2 ∧
      pauliNorm 2 U ^ 4 = ((d : ℝ) ^ (2 * n))⁻¹ *
        (((Fintype.card (DiscretePhaseSpace d n) : ℝ))⁻¹ *
          ∑ h : DiscretePhaseSpace d n, ‖(pauliDeriv h U).trace‖ ^ 2)) := by sorry

end CliffordHierTest
