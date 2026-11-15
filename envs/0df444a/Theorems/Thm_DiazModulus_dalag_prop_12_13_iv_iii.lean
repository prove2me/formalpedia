-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13_iv_iii
-- name    : DiazModulus.dalag_prop_12_13_iv_iii
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-15T05:43:44.663014+00:00
-- url     : https://prove2.me/theorems/ccacc02a-79bf-4488-8f80-78279cb7920b
-- title:
--   DALAG Prop. 12.13 (iv) ⇒ (iii): if every matrix over E has rank equal to its structural rank, no non-zero homogeneous polynomial vanishes at k-free elements of E
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace with the following property (condition (iv) of DALAG Prop. 12.13, in presentation form): whenever $e_1, \dots, e_m \in E$ are linearly independent over $k$, $N_1, \dots, N_m$ are matrices with entries in $k$, and $M = \sum_j e_j N_j$, the rank of $M$ equals the rank of $\sum_j Z_j N_j$ over $k(Z_1, \dots, Z_m)$.
--
--   Let $x_0, \dots, x_n \in E$ be linearly independent over $k$, and let $P \in k[X_0, \dots, X_n]$ be a non-zero homogeneous polynomial. Then $P(x_0, \dots, x_n) \neq 0$. That is condition (iii): $x_1/x_0, \dots, x_n/x_0$ are algebraically independent over $k$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13, implication (iv) ⇒ (iii) (p. 430), with (iv) taken in presentation form and k ⊆ E not assumed. The printed proof applies (iv) to a matrix whose entries need not lie in E; here it is applied to x₀M, whose entries do, through DiazModulus.dalag_prop_12_10 and DiazModulus.dalag_lemma_12_9_dehomog. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_13_iv_iii {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hiv : ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
      (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e → (∀ j, e j ∈ E) →
      M = ∑ j, e j • (N j).map (algebraMap k K) →
      M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank)
    {n D : ℕ} (x : Fin (n + 1) → K) (hx : LinearIndependent k x) (hxE : ∀ i, x i ∈ E)
    (P : MvPolynomial (Fin (n + 1)) k) (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    MvPolynomial.aeval x P ≠ 0 := by
  sorry

end DiazModulus
