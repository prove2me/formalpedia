-- Prove2me | Theorems.Thm_DiazModulus_exists_isWeaklyRegular_vanishing
-- name    : DiazModulus.exists_isWeaklyRegular_vanishing
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T18:16:06.649249+00:00
-- url     : https://prove2.me/theorems/0c231382-03f3-4bbb-9364-30ec18f5a859
-- title:
--   For a finite set of variables $\sigma$ and a point $a \in R^\sigma$, the polynomials $X_i - a_i$ form a weakly regular sequence of length $|\sigma|$ in $R[X_\sigma]$ vanishing at $a$
-- statement:
--   Let $R$ be a commutative ring, $\sigma$ a finite type and $a \in R^\sigma$. Then there is a list of $|\sigma|$ polynomials in $R[X_\sigma]$ (`MvPolynomial σ R`), each vanishing at $a$, which is a weakly regular sequence on $R[X_\sigma]$: the $X_i - a_i$, $i \in \sigma$, in some order. A list $r_1, \dots, r_n$ of elements of a commutative ring $S$ is weakly regular on $S$ when each $r_i$ is a nonzerodivisor on $S/(r_1, \dots, r_{i-1})$ (Mathlib's `IsWeaklyRegular`; the last quotient may be zero).
--
--   **Proof.** For one variable: $X - b$ is monic, hence a nonzerodivisor of $R[X]$, and $R[X]/(X - b) \cong R$ as $R$-modules, so $X - b$ followed by the constants of a weakly $R$-regular sequence is weakly regular on $R[X]$. Induction on $n$ through $R[X_0, \dots, X_n] \cong R[X_1, \dots, X_n][X_0]$ shows that $X_0 - a_0, \dots, X_{n-1} - a_{n-1}$ is weakly regular on $R[X_0, \dots, X_{n-1}]$. Renaming the variables along a bijection between $\sigma$ and $\{0, \dots, |\sigma| - 1\}$ gives the statement, since ring isomorphisms carry weakly regular sequences.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical commutative algebra: the variables minus the coordinates of a point form a regular sequence in a polynomial ring. C1.2 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exists_isWeaklyRegular_vanishing {σ R : Type*} [CommRing R] [Finite σ] (a : σ → R) :
    ∃ zs : List (MvPolynomial σ R), zs.length = Nat.card σ ∧ (∀ z ∈ zs, MvPolynomial.eval a z = 0) ∧
      RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ R) zs := by
  sorry

end DiazModulus
