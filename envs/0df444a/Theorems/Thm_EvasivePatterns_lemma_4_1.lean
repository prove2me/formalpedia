-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_4_1
-- name    : EvasivePatterns.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:20.818463+00:00
-- url     : https://prove2.me/theorems/fd63e6af-00a6-47db-a1b9-42d7dcdd93b6
-- title:
--   Lemma 4.1 — norm saturation and factor inversion: $A^\dagger B\sim Q$ or $Q^\dagger$
-- statement:
--   Let $Q \in \mathbb Z[z]$ have constant coefficient $1$, all nonzero coefficients in $\{\pm1\}$, a rigid support $S$, and $\|QQ^*\|_1 = |S|^2$. Let $K \subseteq \mathbb C$ be a finite Galois extension of $\mathbb Q$ in which complex conjugation commutes with all Galois automorphisms. If $Q = AB$ in $K[z]$ with $A$ monic, then
--   $$
--   T = A^\dagger B
--   $$
--   is associated to $Q$ or to $Q^\dagger$ (equal to one of them up to a nonzero scalar).
--
--   Reversing one factor of $Q$ preserves its autocorrelation; the lemma says that, for polynomials with saturated norm and rigid support, this can only reproduce $Q$ or its reversal.
--
--   Differences from the source:
--   - encoding: polynomials in K[z] → complex polynomials with all coefficients in K; reason: the same ring
--   - encoding: associated in K[z] (nonzero scalar in K) → equal up to a nonzero complex scalar; reason: A^†B, Q and Q^† have coefficients in K and Q, Q^† have a coefficient ±1, so the scalar lies in K
--   - generalization: rigid support (every homometric finite set is a translate of S or of its reflection) → Rigid, quantified over nonempty finite integer sets; reason: the empty set, homometric to every singleton, is excluded, so a one-point support counts as rigid; this adds exactly the instance Q = 1 (A = B = 1, A^†B = Q), where the conclusion holds; for |S| ≥ 2 the two notions coincide
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Lemma 4.1, p.5 (PDF p.6), lines 163–165; field class, lines 156–158

import Mathlib
import Definitions.Def_EvasivePatterns_Rigid
import Definitions.Def_EvasivePatterns_l1Norm
import Definitions.Def_EvasivePatterns_dagger
import Definitions.Def_EvasivePatterns_IsCentralConjGalois

namespace EvasivePatterns

/-- **Lemma 4.1 (Norm saturation and factor inversion).** Let `Q ∈ ℤ[z]` have constant coefficient
`1`, all nonzero coefficients in `{±1}`, a rigid support `S`, and `‖QQ^*‖₁ = |S|²`. For `K` as
specified above, if `Q = AB` in `K[z]` with `A` monic, then `T = A^†B` is associated to `Q` or
`Q^†`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Lemma 4.1, printed p. 5 (PDF p. 6), lines 163–165; the field class `K`, lines
157–158.

**Formalization Note** `K ⊆ ℂ` is in the class `IsCentralConjGalois` (finite Galois over `ℚ`,
conjugation central). Polynomials in `K[z]` are complex polynomials whose coefficients lie in `K`;
`Q` is viewed in `ℂ[z]` by the coefficient cast. "Associated" is equality up to a nonzero scalar,
taken in `ℂ`: since `A^†B`, `Q` and `Q^†` have coefficients in `K` and `Q`, `Q^†` have a
coefficient `±1`, any such scalar lies in `K`. The support of `Q` is cast to `ℤ` for `Rigid`;
`Q^* = Q.reverse`; `Q^† = dagger Q` (equal to `Q^*` for integer `Q`). -/
theorem lemma_4_1 (Q : Polynomial ℤ) (hQ0 : Q.coeff 0 = 1)
    (hQpm : ∀ i, Q.coeff i ≠ 0 → Q.coeff i = 1 ∨ Q.coeff i = -1)
    (hrigid : Rigid (Q.support.image (fun n : ℕ => (n : ℤ))))
    (hnorm : l1Norm (Q * Q.reverse) = (Q.support.card : ℤ) ^ 2)
    (K : IntermediateField ℚ ℂ) (hK : IsCentralConjGalois K)
    (A B : Polynomial ℂ) (hA : ∀ i, A.coeff i ∈ K) (hB : ∀ i, B.coeff i ∈ K) (hAmonic : A.Monic)
    (hQAB : Q.map (Int.castRingHom ℂ) = A * B) :
    ∃ u : ℂ, u ≠ 0 ∧
      (dagger A * B = Polynomial.C u * Q.map (Int.castRingHom ℂ) ∨
        dagger A * B = Polynomial.C u * dagger (Q.map (Int.castRingHom ℂ))) := by sorry

end EvasivePatterns
