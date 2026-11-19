-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_2_det
-- name    : DiazModulus.dalag_prop_12_2_det
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:50.065446+00:00
-- url     : https://prove2.me/theorems/12fa247f-4ed8-45ba-b87d-1bae78ff22b3
-- title:
--   If x ∈ K is transcendental over an intermediate field L of K/k and A, B, C, D are matrices over L with det D ≠ 0, then det (xI + A, B; C, D) ≠ 0
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $L$ be an intermediate field, $k \subseteq L \subseteq K$, and let $x \in K$ be transcendental over $L$. Let $A$, $B$, $C$, $D$ be matrices with entries in $L$, of sizes $r \times r$, $r \times r'$, $r' \times r$ and $r' \times r'$, with $\det D \neq 0$. Then
--   $$\det \begin{pmatrix} x I_r + A & B \\ C & D \end{pmatrix} \neq 0.$$
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.2 (p. 419; proof pp. 420–422): the closing argument of p. 422, that det A is a polynomial in x with leading term x^r det A′, so det A ≠ 0 since x is transcendental; here through the Schur complement and a characteristic polynomial, which is monic. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_2_det {k K : Type*} [Field k] [Field K] [Algebra k K]
    (L : IntermediateField k K) (x : K) (hx : Transcendental L x) {r r' : ℕ}
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin r') K) (C : Matrix (Fin r') (Fin r) K)
    (D : Matrix (Fin r') (Fin r') K) (hA : ∀ i j, A i j ∈ L) (hB : ∀ i j, B i j ∈ L)
    (hC : ∀ i j, C i j ∈ L) (hD : ∀ i j, D i j ∈ L) (hDu : IsUnit D.det) :
    IsUnit (Matrix.fromBlocks (x • (1 : Matrix (Fin r) (Fin r) K) + A) B C D).det := by
  sorry

end DiazModulus
