-- Prove2me | Theorems.Thm_CliffordHierTest_lemma_12
-- name    : CliffordHierTest.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:58.037201+00:00
-- url     : https://prove2.me/theorems/2bc45c12-6ebd-44b3-8d3e-0744cd26b316
-- title:
--   Lemma 12 — closure of $\mathcal P^{(k)}$ under Pauli multiplication; levels $0,1,2$ are groups
-- statement:
--   Let $d$ be prime and $a,b\in\mathbb F_d^{2n}$.
--
--   1. For $k\ge1$, if $U\in\mathcal P^{(k)}$ then $W_aUW_b\in\mathcal P^{(k)}$.
--   2. For $0\le k\le2$, if $U\in\mathcal P^{(k)}$ then $U^*\in\mathcal P^{(k)}$.
--   3. For $0\le k\le2$, $\mathcal P^{(k)}$ is a group: it contains $I$ and is closed under products.
--
--   Item 3 is the sentence before Lemma 12; the main inverse theorem uses that $\mathcal P^{(k-2)}$ is a group for $2\le k\le4$.
--
--   Differences from the source:
--
--   - reading: levels 0, 1 and 2 are groups → they contain I and are closed under products (inverses are item 2); reason: these are the group axioms within the unitary group
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.2.2 Lemma 12 and the sentence before it, p.6

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Lemma 12** with the sentence before it (p.6). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For `k ≥ 1`, `U ∈ 𝒫^{(k)}` implies `W_a U W_b ∈ 𝒫^{(k)}`; for `0 ≤ k ≤ 2`, `U ∈ 𝒫^{(k)}` implies
`U* ∈ 𝒫^{(k)}`; and the levels `0, 1, 2` are groups.

**Formalization Note.** `W_a U W_b ∈ 𝒫^{(k)}` is stated as: some element of `𝒫^{(k)}` has
underlying matrix `W_a U W_b`. "Levels 0, 1 and 2 are groups" (the sentence before Lemma 12) is
the third clause: they contain `I` and are closed under products (closure under inverses is the
second clause). `d` prime (§2.1). -/
theorem lemma_12 (d n : ℕ) [Fact (Nat.Prime d)] :
    (∀ (a b : DiscretePhaseSpace d n) (k : ℕ), 1 ≤ k → ∀ U ∈ pauliPoly d n k,
      ∃ V ∈ pauliPoly d n k, (V : QuditOperator d n) =
        cyclicWeyl d n a * (U : QuditOperator d n) * cyclicWeyl d n b) ∧
    (∀ k : ℕ, k ≤ 2 → ∀ U ∈ pauliPoly d n k, star U ∈ pauliPoly d n k) ∧
    (∀ k : ℕ, k ≤ 2 → 1 ∈ pauliPoly d n k ∧
      ∀ U ∈ pauliPoly d n k, ∀ V ∈ pauliPoly d n k, U * V ∈ pauliPoly d n k) := by sorry

end CliffordHierTest
