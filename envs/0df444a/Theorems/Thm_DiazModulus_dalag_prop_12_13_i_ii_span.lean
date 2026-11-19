-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13_i_ii_span
-- name    : DiazModulus.dalag_prop_12_13_i_ii_span
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:36.407992+00:00
-- url     : https://prove2.me/theorems/88842cb1-206f-49c1-90d2-7de751bc18be
-- title:
--   DALAG Prop. 12.13 (i) ⇒ (ii), span form: if b is algebraically independent over k, x₁, …, xₙ lie in span_k(1, b) and 1, x₁, …, xₙ are k-free, then x is algebraically independent
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$).
--
--   Let $(b_j)_{j \in J}$ be a family of elements of $K$, indexed by any set $J$ (finite or not), algebraically independent over $k$. Let $x_1, \dots, x_n$ ($n \ge 0$) be elements of the $k$-vector space spanned by $1$ and the $b_j$, such that $1, x_1, \dots, x_n$ are linearly independent over $k$. Then $x_1, \dots, x_n$ are algebraically independent over $k$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13 (pp. 429–430): the implication (i) ⇒ (ii) for the span of 1 and any algebraically independent family, which also gives the translation xᵢ = cᵢ + eᵢ used for Cor. 12.14; the printed proof reaches (ii) from (i) through (iv) and (iii). The nearest printed argument is Lemma 12.3, (i) ⇒ (ii) (p. 420), by transcendence degrees; here an affine change of variables with an explicit left inverse. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_13_i_ii_span {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*}
    (b : ι → K) (hb : AlgebraicIndependent k b) {n : ℕ} (x : Fin n → K)
    (hxE : ∀ i, x i ∈ Submodule.span k (insert (1 : K) (Set.range b)))
    (hx : LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K)) :
    AlgebraicIndependent k x := by
  sorry

end DiazModulus
