-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_primitive_cone_exp_sum_hasSum
-- name    : BarvinokCount.ShortFormula.primitive_cone_exp_sum_hasSum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:28:58.085407+00:00
-- url     : https://prove2.me/theorems/9f81f53c-c0f8-4326-923a-250494ff24ab
-- title:
--   Proposition 4.1 — for a primitive cone, σ(K; c) = ∏ 1/(1 − exp⟨c, u_i⟩)
-- statement:
--   Let $K=\operatorname{co}\{u_1,\dots,u_k\}\subseteq\mathbb{R}^d$ be a primitive cone with primitive generators $u_1,\dots,u_k\in\mathbb{Z}^d$. Then
--   $$\sigma(K;c)=\prod_{i=1}^k\frac{1}{1-\exp\{\langle c,u_i\rangle\}}$$
--   in the following two senses:
--
--   1. for every $c\in\mathbb{R}^d$ with $\langle c,u_i\rangle<0$ for all $i$, the series $\sum_{x\in K\cap\mathbb{Z}^d}\exp\{\langle c,x\rangle\}$ converges to the product;
--   2. for every regular point $c$ ($\langle c,u_i\rangle\ne0$ for all $i$), the closed form $\sigma(K;c)$ equals the product.
--
--   For primitive cones the generating function is a pure product of geometric series; this is what makes the constant terms of Corollary 4.2 explicit.
--
--   **Formalization Note** Part 1 states the identity where the series converges, part 2 at every regular point of the closed form, which together are the content of the identity of meromorphic functions in the paper.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 773, Proposition 4.1

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_sigma

namespace BarvinokCount.ShortFormula

theorem primitive_cone_exp_sum_hasSum {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsPrimitiveGens u) :
    (∀ c : Fin d → ℝ, (∀ i, c ⬝ᵥ castVec (u i) < 0) →
      HasSum (fun z : {z : Fin d → ℤ // castVec z ∈ cone u} => Real.exp (c ⬝ᵥ castVec z.1))
        (∏ i, 1 / (1 - Real.exp (c ⬝ᵥ castVec (u i))))) ∧
    ∀ c : Fin d → ℝ, IsRegular u c →
      sigma u c = ∏ i, 1 / (1 - Real.exp (c ⬝ᵥ castVec (u i))) := by sorry

end BarvinokCount.ShortFormula
