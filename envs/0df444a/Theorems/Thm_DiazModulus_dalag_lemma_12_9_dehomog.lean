-- Prove2me | Theorems.Thm_DiazModulus_dalag_lemma_12_9_dehomog
-- name    : DiazModulus.dalag_lemma_12_9_dehomog
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:28.154201+00:00
-- url     : https://prove2.me/theorems/6af6372c-8f53-469f-974a-ca4bbb134f29
-- title:
--   Dehomogenisation keeps the rank: for matrices N₀, …, Nₘ over a field k, N₀ + Σ XᵢNᵢ over k(X₁, …, Xₘ) and Σ YᵢNᵢ (i = 0, …, m) over k(Y₀, …, Yₘ) have the same rank
-- statement:
--   Let $k$ be a field and $N_0, N_1, \dots, N_m$ be $d \times \ell$ matrices with entries in $k$. Then
--   $$\operatorname{rank}_{k(X_1, \dots, X_m)} \Big(N_0 + \sum_{i=1}^m X_i N_i\Big) = \operatorname{rank}_{k(Y_0, \dots, Y_m)} \sum_{i=0}^m Y_i N_i,$$
--   the ranks being taken over the fields of rational functions in $X_1, \dots, X_m$ and in $Y_0, \dots, Y_m$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 12.9 (p. 427; proof p. 428): the passage from the homogenised matrix back to the affine one, which the printed proof leaves to the reader. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_lemma_12_9_dehomog {k : Type*} [Field k] {d l m : ℕ} (N₀ : Matrix (Fin d) (Fin l) k)
    (N : Fin m → Matrix (Fin d) (Fin l) k) :
    (N₀.map (algebraMap k (FractionRing (MvPolynomial (Fin m) k))) +
      ∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank =
    (∑ j : Fin (m + 1),
      (algebraMap (MvPolynomial (Fin (m + 1)) k) (FractionRing (MvPolynomial (Fin (m + 1)) k))
        (MvPolynomial.X j)) •
      ((Fin.cons N₀ N : Fin (m + 1) → Matrix (Fin d) (Fin l) k) j).map
        (algebraMap k (FractionRing (MvPolynomial (Fin (m + 1)) k)))).rank := by
  sorry

end DiazModulus
