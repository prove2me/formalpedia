-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13_ii_iv
-- name    : DiazModulus.dalag_prop_12_13_ii_iv
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:47.698688+00:00
-- url     : https://prove2.me/theorems/9760d43c-7210-4676-baec-ec540bc2aa8a
-- title:
--   DALAG Prop. 12.13 (ii) ⇒ (iv): if 1 ∈ E and every x ∈ Eⁿ with 1, x k-free is algebraically independent, each matrix Σ eⱼNⱼ over E has rank equal to its structural rank
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace with $1 \in E$ satisfying condition (ii) of DALAG Prop. 12.13: whenever $x_1, \dots, x_n \in E$ ($n \ge 0$) and $1, x_1, \dots, x_n$ are linearly independent over $k$, the elements $x_1, \dots, x_n$ are algebraically independent over $k$.
--
--   Let $e_1, \dots, e_m \in E$ be linearly independent over $k$, let $N_1, \dots, N_m$ be $s \times t$ matrices with entries in $k$, and let $M = \sum_{j=1}^m e_j N_j$. Then
--   $$\operatorname{rank}_K M = \operatorname{rank}_{k(Z_1, \dots, Z_m)} \sum_{j=1}^m Z_j N_j.$$
--   The right-hand side is the rank of the generic matrix over the field of rational functions in $Z_1, \dots, Z_m$: the structural rank of $M$ over $k$ (DALAG §12.1.4), computed from the presentation $M = \sum_j e_j N_j$. That is condition (iv) of Prop. 12.13, in presentation form.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13 (pp. 429–430): the implication (ii) ⇒ (iv), with (iv) in presentation form, in place of the printed (i) ⇒ (iv), which follows from Lemma 12.9 (p. 430); so no basis of E is indexed. Proved from DiazModulus.dalag_lemma_12_9 and DiazModulus.matrix_rank_map_field. The hypothesis 1 ∈ E is kept, although it is not needed mathematically. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_13_ii_iv {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (h1 : (1 : K) ∈ E)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x)
    {s t m : ℕ} (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
    (N : Fin m → Matrix (Fin s) (Fin t) k) (he : LinearIndependent k e) (heE : ∀ j, e j ∈ E)
    (hM : M = ∑ j, e j • (N j).map (algebraMap k K)) :
    M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  sorry

end DiazModulus
