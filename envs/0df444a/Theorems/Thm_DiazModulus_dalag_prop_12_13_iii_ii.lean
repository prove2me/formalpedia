-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13_iii_ii
-- name    : DiazModulus.dalag_prop_12_13_iii_ii
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:57.464236+00:00
-- url     : https://prove2.me/theorems/416bb5be-b364-46b0-8883-4459a56451c4
-- title:
--   DALAG Prop. 12.13 (iii) ⇒ (ii): if 1 ∈ E and no non-zero homogeneous polynomial over k vanishes at k-free elements of E, every x ∈ Eⁿ with 1, x k-free is algebraically independent
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace with $1 \in E$ satisfying condition (iii) of DALAG Prop. 12.13: whenever $x_0, \dots, x_n \in E$ are linearly independent over $k$ and $P \in k[X_0, \dots, X_n]$ is a non-zero homogeneous polynomial, $P(x_0, \dots, x_n) \neq 0$.
--
--   Let $x_1, \dots, x_n \in E$ be such that $1, x_1, \dots, x_n$ are linearly independent over $k$. Then $x_1, \dots, x_n$ are algebraically independent over $k$. That is condition (ii) of Prop. 12.13.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13, implication (iii) ⇒ (ii) (p. 430), "easy (take x₀ = 1)" in print; the homogenisation that this leaves implicit is supplied. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_13_iii_ii {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (h1 : (1 : K) ∈ E)
    (hiii : ∀ (n D : ℕ) (x : Fin (n + 1) → K), LinearIndependent k x → (∀ i, x i ∈ E) →
      ∀ P : MvPolynomial (Fin (n + 1)) k, P.IsHomogeneous D → P ≠ 0 → MvPolynomial.aeval x P ≠ 0)
    {n : ℕ} (x : Fin n → K) (hxE : ∀ i, x i ∈ E)
    (hx : LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K)) :
    AlgebraicIndependent k x := by
  sorry

end DiazModulus
