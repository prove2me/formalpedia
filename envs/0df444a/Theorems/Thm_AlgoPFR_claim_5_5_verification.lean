-- Prove2me | Theorems.Thm_AlgoPFR_claim_5_5_verification
-- name    : AlgoPFR.claim_5_5_verification
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:05.457326+00:00
-- url     : https://prove2.me/theorems/c085323c-e45a-4448-8b2b-0552cfa55e26
-- title:
--   Claim 5.5 — verifying a candidate coset
-- statement:
--   There are a program and constants $c>0$, $C$, $c'$ such that for every nonempty $A\subseteq\mathbb F_2^n$, all $0<\eta\le1$, $0<\delta<1$, and every affine subspace $a+V'$ given by $a$ and a basis of $V'$, the program with membership and uniform-sample access to $A$ uses at most $C(n+1/\eta+\log(1/\delta)+2)^{c'}$ time, samples and queries, and satisfies:
--
--   1. **Completeness.** It accepts with probability at least $1-\delta$ if ($V'=\{0\}$ or $|V'|\le|A|/2$) and $|A\cap(a+V')|/|A|\ge\eta$.
--   2. **Soundness.** It rejects with probability at least $1-\delta$ unless all of $|V'|\le|A|$, $|A\cap(a+V')|/|A|\ge c\eta$ and $|A\cap(a+V')|/|V'|\ge c\eta$ hold.
--
--   The test is what allows a good trial to be recognized, so that repetition amplifies success.
--
--   Differences from the source:
--
--   - encoding: A ⊆ F₂ⁿ, not stated to be nonempty → A nonempty; reason: |A| is a denominator and a uniform sampler must exist; it excludes only an undefined case
--   - generalization: the algorithm is given η and δ → the program receives only ⌈1/η⌉ and ⌈log₂(1/δ)⌉; reason: less input information, so a stronger existence claim that gives the printed one
--   - encoding: accepts or rejects, and poly(n, 1/η, log(1/δ)), Ω(η) → output [1] or [0]; C(n + 1/η + log₂(1/δ) + 2)^c′; c before n, A, η, δ; reason: the machine's output convention and universal constants
--   - encoding: an affine representation of a + V′ → the input a, the length of a linearly independent list L, and L, with V′ = span L; reason: the machine's input convention for a point and a basis
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 5.5, p.45

import Mathlib
import Definitions.Def_AlgoPFR_Machine

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 5.5.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.45: for `A ⊆ F₂ⁿ`, `0 < η ≤ 1`, `0 < δ < 1`, an algorithm with membership-oracle
and uniform-sample access to `A`, given an affine representation of `a + V′`, satisfies: *completeness*, it
accepts with probability at least `1 − δ` if (`V′ = {0}` or `|V′| ≤ |A|/2`) and `|A ∩ (a + V′)|/|A| ≥ η`;
*soundness*, it rejects with probability at least `1 − δ` if `a + V′` does not satisfy `|V′| ≤ |A|`,
`|A ∩ (a + V′)|/|A| = Ω(η)`, `|A ∩ (a + V′)|/|V′| = Ω(η)`. It uses `poly(n, 1/η, log(1/δ))` time, samples
and queries.

**Formalization Note.** `A` is nonempty: `|A|` is a denominator and a uniform sampler must exist. The
claim's `η` is called `e` here, to keep it apart from the constant of Theorem 4.3. The input is
`n, a, ⌈1/e⌉, ⌈log₂(1/δ)⌉`, the length of the basis, and the basis; the output is `[1]` (accept) or
`[0]` (reject). The `Ω(·)` constant `c` is universal. -/
theorem claim_5_5_verification :
    ∃ (P : Program) (c C : ℝ) (c' : ℕ), 0 < c ∧ ∀ (n : ℕ) (A : Finset (Vec n)) (hA : A.Nonempty)
      (e δ : ℝ) (a : Vec n) (L : List (Vec n)), 0 < e → e ≤ 1 → 0 < δ → δ < 1 → IsBasisList L →
      (∀ ω : Tape n, IsRunTape A ω →
        HaltsWithin n P (memberRate A)
          (n :: encodeVec a :: ⌈1 / e⌉₊ :: ⌈Real.logb 2 (1 / δ)⌉₊ :: L.length :: L.map encodeVec) ω
          (C * ((n : ℝ) + 1 / e + Real.logb 2 (1 / δ) + 2) ^ c')) ∧
      (((listSpan L = ⊥ ∨ 2 * subspaceCard (listSpan L) ≤ A.card) ∧
          e * A.card ≤ cosetCount A a (listSpan L)) →
        ProbAtLeast (tapeMeasure (uniformLaw A hA))
          {ω | Outputs n P (memberRate A)
            (n :: encodeVec a :: ⌈1 / e⌉₊ :: ⌈Real.logb 2 (1 / δ)⌉₊ :: L.length :: L.map encodeVec) ω [1]}
          (1 - δ)) ∧
      (¬ (subspaceCard (listSpan L) ≤ A.card ∧
            c * e * A.card ≤ cosetCount A a (listSpan L) ∧
            c * e * subspaceCard (listSpan L) ≤ cosetCount A a (listSpan L)) →
        ProbAtLeast (tapeMeasure (uniformLaw A hA))
          {ω | Outputs n P (memberRate A)
            (n :: encodeVec a :: ⌈1 / e⌉₊ :: ⌈Real.logb 2 (1 / δ)⌉₊ :: L.length :: L.map encodeVec) ω [0]}
          (1 - δ)) := by sorry

end AlgoPFR
