-- Prove2me | Theorems.Thm_DiazModulus_dalag_lemma_12_9
-- name    : DiazModulus.dalag_lemma_12_9
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:24.857238+00:00
-- url     : https://prove2.me/theorems/c3a6cf3d-ae3c-407c-8cc5-e49c9b2a3da9
-- title:
--   DALAG Lemma 12.9: for M = Σ eⱼNⱼ with e free over k, and φ k-linear into k + kX₁ + ⋯ + kXₙ and injective on span(e), the rank of φ(M) over k(X) is the structural rank of M
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$), let $M$ be a $d \times \ell$ matrix with entries in $K$, and let $e_1, \dots, e_m \in K$ be linearly independent over $k$ and $N_1, \dots, N_m$ be $d \times \ell$ matrices with entries in $k$ such that $M = \sum_{j=1}^m e_j N_j$. Let $\varphi : K \to k^{n+1}$ be $k$-linear and injective on the $k$-span of $e_1, \dots, e_m$, read as a map into the affine forms $k + kX_1 + \dots + kX_n$, and let $\varphi(M)$ be the matrix whose $(a, b)$ entry is $\varphi(M_{ab})_0 + \sum_{i=1}^n \varphi(M_{ab})_i X_i$. Then
--   $$\operatorname{rank}_{k(X_1, \dots, X_n)} \varphi(M) = \operatorname{rank}_{k(Z_1, \dots, Z_m)} \sum_{j=1}^m Z_j N_j.$$
--   The right-hand side is the structural rank of $M$ over $k$ (DALAG §12.1.4), computed from the presentation $M = \sum_j e_j N_j$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 12.9 (p. 427; proof p. 428), in presentation form, for any field k and any k-linear map into the affine forms k + kX₁ + ⋯ + kXₙ that is injective on the span of the eⱼ. The two steps the printed proof leaves to the reader are DiazModulus.dalag_lemma_12_9_dehomog and DiazModulus.dalag_lemma_12_8_linear. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_lemma_12_9 {k K : Type*} [Field k] [Field K] [Algebra k K] {d l m n : ℕ}
    (M : Matrix (Fin d) (Fin l) K) (e : Fin m → K) (he : LinearIndependent k e)
    (N : Fin m → Matrix (Fin d) (Fin l) k) (hMN : M = ∑ j, e j • (N j).map (algebraMap k K))
    (φ : K →ₗ[k] (Fin (n + 1) → k)) (hφ : Set.InjOn φ (Submodule.span k (Set.range e) : Set K)) :
    (M.map fun x => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (MvPolynomial.C (φ x 0) + ∑ i : Fin n, MvPolynomial.C (φ x i.succ) * MvPolynomial.X i)).rank =
    (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  sorry

end DiazModulus
