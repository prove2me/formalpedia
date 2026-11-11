-- Prove2me | Theorems.Thm_FasterPrimeEnum_lemma_2_10
-- name    : FasterPrimeEnum.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:37:53.001169+00:00
-- url     : https://prove2.me/theorems/f0234e9a-4647-4d09-8f1e-657aa7cec6f5
-- title:
--   Lemma 2.10 — the ideals of $\mathbb Z[\sqrt{-1}]$ of odd norm $n$
-- statement:
--   Let $n\ge1$ be odd. The map $(a,b)\mapsto\langle a+2b\sqrt{-1}\rangle$ is a bijection from
--
--   $$
--   \{(a,b)\in\mathbb Z^2:\ a^2+4b^2=n,\ a\ge1\}
--   $$
--
--   to the set of ideals of $\mathbb Z[\sqrt{-1}]$ of norm $n$.
--
--   It gives a standard generator for each ideal of odd norm, and so turns the ideal count $\psi_{-1}(n)$ into a count of representations by a binary quadratic form, which is how Proposition 2.9 is proved.
--
--   **Formalization Note** $\mathbb Z[\sqrt{-1}]$ is Mathlib's `ℤ√(-1)`, $\langle\theta\rangle$ is the principal ideal of $\theta$, and the norm of an ideal is its index.
--
--   Differences from the source:
--   - encoding: ideals of Z[√-1] of norm n → ideals I of ℤ√(-1) with Nat.card (ℤ√(-1) ⧸ I) = n; reason: the norm of a nonzero ideal is its index; the zero ideal has infinite index
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Lemma 2.10, p.16

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **Lemma 2.10** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.16.

"Let n ⩾ 1 be odd. The map (a, b) ↦ ⟨a + 2b√−1⟩ is a bijection from {(a, b) ∈ Z² : a² + 4b² = n, a ⩾ 1} to the set of ideals of
Z[√−1] of norm n."

**Formalization Note.** `Z[√−1]` is Mathlib's `ℤ√(-1)`, whose element `⟨x, y⟩` is `x + y√−1`;
`⟨θ⟩` is the principal ideal `Ideal.span {θ}`. The norm of an ideal is its index
`Nat.card (ℤ√(-1) ⧸ I)`. An odd natural number is at least `1`. -/
theorem lemma_2_10 (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun ab : ℤ × ℤ => Ideal.span {(⟨ab.1, 2 * ab.2⟩ : ℤ√(-1))})
      {ab : ℤ × ℤ | ab.1 ^ 2 + 4 * ab.2 ^ 2 = (n : ℤ) ∧ 1 ≤ ab.1}
      {I : Ideal (ℤ√(-1)) | Nat.card (ℤ√(-1) ⧸ I) = n} := by sorry

end FasterPrimeEnum
