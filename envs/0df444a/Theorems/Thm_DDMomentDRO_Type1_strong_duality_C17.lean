-- Prove2me | Theorems.Thm_DDMomentDRO_Type1_strong_duality_C17
-- name    : DDMomentDRO.Type1.strong_duality_C17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:24.951325+00:00
-- url     : https://prove2.me/theorems/e42c9153-3859-4cd3-a770-65ce2d03cbee
-- title:
--   Proof of Theorem 1, p. 36 — when (C-17) is feasible, strong duality holds with a primal and a dual optimum
-- statement:
--   Fix a stage of the Bellman equation (2) under the Type 1 ambiguity set $\mathcal P^{D_1}(x)$ of (3) (with $p\ge0$, as in (C-17f)), and a state $x$ at which $\mathcal P^{D_1}(x)$ is nonempty. Then there are $p\in\mathcal P^{D_1}(x)$ and nonnegative $\alpha,\beta\in\mathbb R^m$, $\underline\gamma,\bar\gamma\in\mathbb R^K$ with
--   $$(-\alpha+\beta)^{\mathsf T} f(\xi^k)-\underline\gamma_k+\bar\gamma_k\ \ge\ Q_{t+1}(x,\xi^k)\qquad\text{for every }k\in[K]$$
--   such that
--   $$\sum_{k=1}^K p_k\,Q_{t+1}(x,\xi^k)\ =\ -\alpha^{\mathsf T}l(x)+\beta^{\mathsf T}u(x)-\underline\gamma^{\mathsf T}\underline p(x)+\bar\gamma^{\mathsf T}\bar p(x).$$
--
--   Combined with weak duality, $p$ attains the inner maximum of (2) at $x$ and $(\alpha,\beta,\underline\gamma,\bar\gamma)$ attains the minimum of the dual (4b), (4d): the two optimal values are equal and both are attained.
--
--   **Formalization Note** The stage set $S$ and the binary-state hypothesis are carried as standing binders of the mission; the statement does not depend on them.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 36, proof of Theorem 1, (C-17)

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting

namespace DDMomentDRO.Type1

open Matrix

/-- Strong duality for the inner LP (C-17) under the Type 1 set (3): if the ambiguity set at
the state `x` is nonempty, there are a feasible `p` and a dual point `(α, β, γ̲, γ̄)` satisfying
(4b), (4d) at `x` whose objective values coincide. -/
theorem strong_duality_C17 {I J K m : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (x : Fin I → ℝ) (hne : (amb1 ξ e l u pl pu x).Nonempty) :
    ∃ p ∈ amb1 ξ e l u pl pu x, ∃ (α β : Fin m → ℝ) (γl γu : Fin K → ℝ),
      DualFeas1 Qn ξ e x α β γl γu ∧
      ∑ k, p k * Qn x k = -(α ⬝ᵥ l x) + β ⬝ᵥ u x - γl ⬝ᵥ pl x + γu ⬝ᵥ pu x := by sorry

end DDMomentDRO.Type1
