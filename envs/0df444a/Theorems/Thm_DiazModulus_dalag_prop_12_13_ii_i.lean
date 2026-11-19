-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13_ii_i
-- name    : DiazModulus.dalag_prop_12_13_ii_i
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:48.206644+00:00
-- url     : https://prove2.me/theorems/11805516-29d4-4e72-ae18-b279560ea539
-- title:
--   DALAG Prop. 12.13 (ii) ⇒ (i): if 1 ∈ E and every x ∈ Eⁿ with 1, x k-free is algebraically independent, E has a k-basis {1} ∪ B with B algebraically independent over k
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace with $1 \in E$ satisfying condition (ii) of DALAG Prop. 12.13: whenever $x_1, \dots, x_n \in E$ ($n \ge 0$) and $1, x_1, \dots, x_n$ are linearly independent over $k$, the elements $x_1, \dots, x_n$ are algebraically independent over $k$.
--
--   Then $E$ has a basis $(b_i)_{i \in I}$ over $k$ with an index $i_0 \in I$ such that $b_{i_0} = 1$ and the family $(b_i)_{i \in I,\, i \neq i_0}$ is algebraically independent over $k$. That is condition (i) of Prop. 12.13. The index set $I$ is a type in the universe of $K$; this is no restriction, since a basis of $E$ can be indexed by a subset of $E$. $E$ may be infinite-dimensional.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13, implication (ii) ⇒ (i) (p. 430), "plain" in print. The basis extends {1}; algebraic independence is checked on finite subfamilies, so E may be infinite-dimensional. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

universe u v

theorem dalag_prop_12_13_ii_i {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (E : Submodule k K) (h1 : (1 : K) ∈ E)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x) :
    ∃ (ι : Type v) (b : Module.Basis ι k ↥E) (i₀ : ι),
      (b i₀ : K) = 1 ∧ AlgebraicIndependent k (fun i : {i : ι // i ≠ i₀} => (b i : K)) := by
  sorry

end DiazModulus
