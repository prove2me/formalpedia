-- Prove2me | Theorems.Thm_AccelVI_SafeAVI_error_le_residual
-- name    : AccelVI.SafeAVI.error_le_residual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:20.704462+00:00
-- url     : https://prove2.me/theorems/fa7f2f45-c373-4327-addc-9b29f5edf175
-- title:
--   Proof of Theorem 7.1, p. 14 — ‖v − v*‖∞ ≤ (1 − λ)⁻¹ ‖v − T(v)‖∞
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a valid finite MDP with a nonempty action set and Bellman operator $T$, and let $v^*$ be a fixed point of $T$, $T(v^*) = v^*$. Then for every $v\in\mathbb R^{\mathbb S}$,
--
--   $$\|v - v^*\|_\infty \le (1-\lambda)^{-1}\,\|v - T(v)\|_\infty .$$
--
--   The distance to the optimal value function is thus controlled by the Bellman residual, which is computable. In the proof of Theorem 7.1 this converts the geometric decay of the residual into the geometric decay of the error.
--
--   **Formalization Note** The paper applies the bound to the iterates $v_s$; nothing about them is used, so it is stated for an arbitrary vector $v$. The paper's line drops a parenthesis ($\|v_s - T(v_s\|_\infty$); the intended $\|v_s - T(v_s)\|_\infty$ is stated. $v^*$ (the unique fixed point of $T$, p. 3) enters as a vector with $T(v^*) = v^*$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 14, proof of Theorem 7.1, sentence after the display of ‖v_s − v*‖∞

import Mathlib
import Definitions.Def_AccelVI_SafeAVI_Setting

namespace AccelVI.SafeAVI
theorem error_le_residual {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (vstar : S → ℝ) (hfix : bellman M vstar = vstar) (v : S → ℝ) :
    ‖v - vstar‖ ≤ (1 - M.lam)⁻¹ * ‖v - bellman M v‖ := by sorry
end AccelVI.SafeAVI
