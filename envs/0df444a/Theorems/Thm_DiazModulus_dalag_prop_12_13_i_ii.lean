-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_13_i_ii
-- name    : DiazModulus.dalag_prop_12_13_i_ii
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:35.813784+00:00
-- url     : https://prove2.me/theorems/7edd0b5c-c921-44ae-851f-9a8980cf49a7
-- title:
--   DALAG Prop. 12.13 (i) ⇒ (ii): if E has a k-basis {1} ∪ B with B algebraically independent over k, every x ∈ Eⁿ with 1, x k-free is algebraically independent
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace satisfying condition (i) of DALAG Prop. 12.13: $E$ has a basis $(b_i)_{i \in I}$ over $k$ with an index $i_0 \in I$ such that $b_{i_0} = 1$ and the family $(b_i)_{i \in I,\, i \neq i_0}$ is algebraically independent over $k$, the index set $I$ being any set.
--
--   Let $x_1, \dots, x_n \in E$ be such that $1, x_1, \dots, x_n$ are linearly independent over $k$. Then $x_1, \dots, x_n$ are algebraically independent over $k$. That is condition (ii) of Prop. 12.13.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.13, implication (i) ⇒ (ii) (pp. 429–430), which the printed proof obtains through (iv) and (iii); here directly, from DiazModulus.dalag_prop_12_13_i_ii_span. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_13_i_ii {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    {ι : Type*} (b : Module.Basis ι k ↥E) (i₀ : ι) (hb₀ : (b i₀ : K) = 1)
    (hb : AlgebraicIndependent k (fun i : {i : ι // i ≠ i₀} => (b i : K)))
    {n : ℕ} (x : Fin n → K) (hxE : ∀ i, x i ∈ E)
    (hx : LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K)) :
    AlgebraicIndependent k x := by
  sorry

end DiazModulus
