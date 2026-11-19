-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_12_14
-- name    : DiazModulus.dalag_cor_12_14
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:54.569658+00:00
-- url     : https://prove2.me/theorems/76a6e58d-dbc3-43fa-8ca9-0e5e765dad9b
-- title:
--   Waldschmidt 2000 (DALAG), Cor. 12.14: if E₀ ∩ k = {0}, then k-free elements of E₀ are algebraically independent iff every matrix over k + E₀ has rank equal to its structural rank
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E_0 \subseteq K$ be a $k$-vector subspace with $E_0 \cap k = \{0\}$: if $c \in k$ and $c \cdot 1 \in E_0$, then $c = 0$. Write $k + E_0$ for the $k$-vector space spanned by $1$ and $E_0$. The following are equivalent.
--
--   (i) Whenever $x_1, \dots, x_n \in E_0$ are linearly independent over $k$, they are algebraically independent over $k$.
--
--   (ii) Whenever $e_1, \dots, e_m \in k + E_0$ are linearly independent over $k$ and $N_1, \dots, N_m$ are $s \times t$ matrices with entries in $k$, the matrix $M = \sum_{j=1}^m e_j N_j$ satisfies
--   $$\operatorname{rank}_K M = \operatorname{rank}_{k(Z_1, \dots, Z_m)} \sum_{j=1}^m Z_j N_j.$$
--   The right-hand side is the rank of the generic matrix over the field of rational functions in $Z_1, \dots, Z_m$: the structural rank of $M$ over $k$ (DALAG §12.1.4), computed from the presentation $M = \sum_j e_j N_j$. So (ii) says that every matrix with entries in $k + E_0$ has rank equal to its structural rank, in presentation form.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.14 (p. 430), with (ii) in presentation form. No proof is printed; the text applies Prop. 12.13 to k + E₀. The implication (i) ⇒ (ii) holds without the hypothesis E₀ ∩ k = {0}, which is used only for (ii) ⇒ (i). Proved from DiazModulus.dalag_prop_12_13_i_ii_span, DiazModulus.dalag_prop_12_13_ii_iv, DiazModulus.dalag_prop_12_13_iv_iii and DiazModulus.dalag_prop_12_13_iii_ii. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_12_14 {k K : Type*} [Field k] [Field K] [Algebra k K] (E₀ : Submodule k K)
    (hE₀ : ∀ c : k, algebraMap k K c ∈ E₀ → c = 0) :
    (∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E₀) → LinearIndependent k x →
        AlgebraicIndependent k x) ↔
      ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
        (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e →
        (∀ j, e j ∈ Submodule.span k {(1 : K)} ⊔ E₀) →
        M = ∑ j, e j • (N j).map (algebraMap k K) →
        M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k)
          (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) •
            (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  sorry

end DiazModulus
