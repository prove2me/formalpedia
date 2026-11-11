-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_lemma_F_7_1
-- name    : BlockOrthoCSP.Decide.lemma_F_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:13:07.15196+00:00
-- url     : https://prove2.me/theorems/f3473f39-5f80-4b59-b7fb-5eba67fd4036
-- title:
--   Lemma F.7.1 — finitely many nonempty multisets of nonzero algebraic numbers have infinitely many common exponents with all power sums nonzero; one is computable
-- statement:
--   Let $A_1,\dots,A_t$ be nonempty finite multisets of nonzero algebraic complex numbers. There are infinitely many integers $m \ge 1$ with
--   $$\sum_{a \in A_i} a^m \ne 0 \quad \text{for every } i \in [t], \qquad (F.41)$$
--   and such an $m$ can be found by enumerating the positive integers and performing exact algebraic zero tests: one computable function sends exact codes of the multisets (lists of algebraic-number codes) to such an $m$.
--
--   Differences from the source:
--   - encoding: C^× (nonzero algebraic complex numbers) → a ∈ ℂ with a ≠ 0 and IsAlgebraic ℚ a; reason: the paper's C is the algebraic numbers in ℂ
--   - encoding: nonempty finite multisets A_1, …, A_t → A : Fin t → Multiset ℂ with A i ≠ 0; for the algorithm, lists of valid AlgCodes (a list is a multiset with an order); reason: same objects; repeated elements count in both
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
--   - reading: 'such an m can be found by enumerating the positive integers and performing exact algebraic zero tests' → a computable map from codes of the multisets to an m ≥ 1 satisfying (F.41); reason: the enumeration is the paper's witness; the clause asserts that some m is effectively found
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-29, Lemma F.7.1

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Codes

namespace BlockOrthoCSP.Decide

/-- Lemma F.7.1, p. F-29: nonempty finite multisets `A_1, …, A_t` of nonzero (algebraic) complex
numbers have infinitely many common exponents `m ≥ 1` with every power sum nonzero; and such an
`m` is computable from exact codes of the multisets. -/
theorem lemma_F_7_1 :
    (∀ (t : ℕ) (A : Fin t → Multiset ℂ), (∀ i, A i ≠ 0) →
      (∀ i, ∀ a ∈ A i, a ≠ 0 ∧ IsAlgebraic ℚ a) →
        Set.Infinite {m : ℕ | 1 ≤ m ∧ ∀ i, ((A i).map (· ^ m)).sum ≠ 0}) ∧
    ∃ f : List (List AlgCode) → ℕ, Computable f ∧
      ∀ cs : List (List AlgCode), (∀ l ∈ cs, l ≠ [] ∧ ∀ c ∈ l, c.Valid ∧ c.val ≠ 0) →
        1 ≤ f cs ∧ ∀ l ∈ cs, (l.map fun c => c.val ^ f cs).sum ≠ 0 := by sorry

end BlockOrthoCSP.Decide
