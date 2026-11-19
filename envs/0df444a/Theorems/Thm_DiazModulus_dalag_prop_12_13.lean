-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13
-- name    : DiazModulus.dalag_prop_12_13
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:06.540915+00:00
-- url     : https://prove2.me/theorems/b262b067-8b34-4b7b-909a-3f8521261dde
-- title:
--   Waldschmidt 2000 (DALAG), Prop. 12.13: for E ⊇ k, equivalent: a basis 1 ∪ {alg. indep.}; 1, x k-free ⇒ x alg. indep.; P(x) ≠ 0 for homogeneous P ≠ 0; rank = structural rank
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace with $1 \in E$ (that is, $E$ contains $k$). The following four conditions are equivalent.
--
--   (i) $E$ has a basis $(b_i)_{i \in I}$ over $k$ with an index $i_0 \in I$ such that $b_{i_0} = 1$ and the family $(b_i)_{i \in I,\, i \neq i_0}$ is algebraically independent over $k$.
--
--   (ii) Whenever $x_1, \dots, x_n \in E$ ($n \ge 0$) and $1, x_1, \dots, x_n$ are linearly independent over $k$, the elements $x_1, \dots, x_n$ are algebraically independent over $k$.
--
--   (iii) Whenever $x_0, \dots, x_n \in E$ are linearly independent over $k$ and $P \in k[X_0, \dots, X_n]$ is a non-zero homogeneous polynomial, $P(x_0, \dots, x_n) \neq 0$.
--
--   (iv) Whenever $e_1, \dots, e_m \in E$ are linearly independent over $k$ and $N_1, \dots, N_m$ are $s \times t$ matrices with entries in $k$, the matrix $M = \sum_{j=1}^m e_j N_j$ satisfies $\operatorname{rank}_K M = \operatorname{rank}_{k(Z_1, \dots, Z_m)} \sum_{j=1}^m Z_j N_j$.
--
--   In (i), the index set $I$ is a type in the universe of $K$; this is no restriction, since a basis of $E$ can be indexed by a subset of $E$. $E$ may be infinite-dimensional. In (iv), the right-hand side is the structural rank of $M$ over $k$ (DALAG §12.1.4).
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13 (pp. 429–430), for a subspace E containing k, written 1 ∈ E, with (iv) in presentation form. The equivalence is proved along the cycle (i) ⇒ (ii) ⇒ (iv) ⇒ (iii) ⇒ (ii) ⇒ (i), with (ii) ⇒ (iv) in place of the printed (i) ⇒ (iv) through Lemma 12.9; (iv) ⇒ (iii) is DiazModulus.dalag_prop_12_13_iv_iii. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

universe u v

theorem dalag_prop_12_13 {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (E : Submodule k K) (h1 : (1 : K) ∈ E) :
    List.TFAE
      [∃ (ι : Type v) (b : Module.Basis ι k ↥E) (i₀ : ι),
          (b i₀ : K) = 1 ∧ AlgebraicIndependent k (fun i : {i : ι // i ≠ i₀} => (b i : K)),
        ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
          LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x,
        ∀ (n D : ℕ) (x : Fin (n + 1) → K), LinearIndependent k x → (∀ i, x i ∈ E) →
          ∀ P : MvPolynomial (Fin (n + 1)) k, P.IsHomogeneous D → P ≠ 0 →
            MvPolynomial.aeval x P ≠ 0,
        ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
          (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e → (∀ j, e j ∈ E) →
          M = ∑ j, e j • (N j).map (algebraMap k K) →
          M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k)
            (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) •
              (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank] := by
  sorry

end DiazModulus
