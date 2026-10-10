-- Prove2me | Theorems.Thm_DDMomentDRO_Type1_weak_duality_C17
-- name    : DDMomentDRO.Type1.weak_duality_C17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:46:57.257414+00:00
-- url     : https://prove2.me/theorems/f41f7350-3a2c-4c89-a6db-2b67ba98310f
-- title:
--   Proof of Theorem 1, p. 36 — weak duality for the inner LP (C-17) against the dual (4b), (4d)
-- statement:
--   Fix a stage of the Bellman equation (2) under the Type 1 ambiguity set $\mathcal P^{D_1}(x)$ of (3) (with $p\ge0$, as in (C-17f)), and a state $x$. Let $p\in\mathcal P^{D_1}(x)$, and let $\alpha,\beta\in\mathbb R^m$, $\underline\gamma,\bar\gamma\in\mathbb R^K$ be nonnegative with
--   $$(-\alpha+\beta)^{\mathsf T} f(\xi^k)-\underline\gamma_k+\bar\gamma_k\ \ge\ Q_{t+1}(x,\xi^k)\qquad\text{for every }k\in[K].$$
--   Then
--   $$\sum_{k=1}^K p_k\,Q_{t+1}(x,\xi^k)\ \le\ -\alpha^{\mathsf T}l(x)+\beta^{\mathsf T}u(x)-\underline\gamma^{\mathsf T}\underline p(x)+\bar\gamma^{\mathsf T}\bar p(x).$$
--
--   This is the weak half of the LP duality between the inner maximization (C-17) of (2) and the dual whose constraints are (4b), (4d): every dual feasible point bounds the worst-case expectation from above.
--
--   **Formalization Note** The stage set $S$ and the binary-state hypothesis are carried as standing binders of the mission; the statement does not depend on them.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 36, proof of Theorem 1, (C-17)

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting

namespace DDMomentDRO.Type1

open Matrix

/-- Weak duality for the inner LP (C-17) of the Bellman equation (2) under the Type 1 set (3):
for a state `x`, every `p` in the ambiguity set and every dual point `(α, β, γ̲, γ̄)` satisfying
(4b), (4d) at `x`, `∑ₖ pₖ Q_{t+1}(x, ξᵏ) ≤ −αᵀl(x) + βᵀu(x) − γ̲ᵀp̲(x) + γ̄ᵀp̄(x)`. -/
theorem weak_duality_C17 {I J K m : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) (hp : p ∈ amb1 ξ e l u pl pu x)
    (α β : Fin m → ℝ) (γl γu : Fin K → ℝ) (hdual : DualFeas1 Qn ξ e x α β γl γu) :
    ∑ k, p k * Qn x k ≤ -(α ⬝ᵥ l x) + β ⬝ᵥ u x - γl ⬝ᵥ pl x + γu ⬝ᵥ pu x := by sorry

end DDMomentDRO.Type1
