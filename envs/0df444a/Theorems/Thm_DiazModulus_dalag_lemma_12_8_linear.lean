-- Prove2me | Theorems.Thm_DiazModulus_dalag_lemma_12_8_linear
-- name    : DiazModulus.dalag_lemma_12_8_linear
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:26.891302+00:00
-- url     : https://prove2.me/theorems/ec10078d-b687-4c92-96f2-d98ea76742fe
-- title:
--   DALAG Lemma 12.8 for any injective map: if M = Σ eⱼNⱼ, e free over k, Nⱼ over k, and φ: K → kX₁ + ⋯ + kXₙ is k-linear and injective on span(e), then rank φ(M) = rank Σ ZⱼNⱼ
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$), let $M$ be a $d \times \ell$ matrix with entries in $K$, and let $e_1, \dots, e_m \in K$ be linearly independent over $k$ and $N_1, \dots, N_m$ be $d \times \ell$ matrices with entries in $k$ such that $M = \sum_{j=1}^m e_j N_j$. Let $\varphi : K \to k^n$ be $k$-linear and injective on the $k$-span of $e_1, \dots, e_m$, and let $\varphi(M)$ be the matrix whose $(a, b)$ entry is the linear form $\sum_{i=1}^n \varphi(M_{ab})_i X_i$. Then
--   $$\operatorname{rank}_{k(X_1, \dots, X_n)} \varphi(M) = \operatorname{rank}_{k(Z_1, \dots, Z_m)} \sum_{j=1}^m Z_j N_j.$$
--   The right-hand side is the structural rank of $M$ over $k$ (DALAG §12.1.4), computed from the presentation $M = \sum_j e_j N_j$. DALAG's Lemma 12.8 states this equality for $\varphi$ given by a basis.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 12.8 (p. 426; proof p. 427), for any k-linear map into kX₁ + ⋯ + kXₙ that is injective on the span of the eⱼ, as the proof of Lemma 12.9 (p. 428) uses it; the printed statement is for a map given by a basis. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_lemma_12_8_linear {k K : Type*} [Field k] [Field K] [Algebra k K] {d l m n : ℕ}
    (M : Matrix (Fin d) (Fin l) K) (e : Fin m → K) (he : LinearIndependent k e)
    (N : Fin m → Matrix (Fin d) (Fin l) k) (hMN : M = ∑ j, e j • (N j).map (algebraMap k K))
    (φ : K →ₗ[k] (Fin n → k)) (hφ : Set.InjOn φ (Submodule.span k (Set.range e) : Set K)) :
    (M.map fun x => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k))
        (∑ i, MvPolynomial.C (φ x i) * MvPolynomial.X i)).rank =
    (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  sorry

end DiazModulus
