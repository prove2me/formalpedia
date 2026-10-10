-- Prove2me | Theorems.Thm_DDMomentDRO_Type3_dual_function_C22
-- name    : DDMomentDRO.Type3.dual_function_C22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:17.048138+00:00
-- url     : https://prove2.me/theorems/27536222-da4c-4a09-aecc-eebdd443411b
-- title:
--   Proof of Theorem 3, pp. 38–39 — the dual function of (C-20): maximizing the Lagrangian over p ≥ 0, τ
-- statement:
--   Fix a state $x$ and dual variables $(s,u,z_1,z_2,z_3,Y)$, and consider the set of Lagrangian values $\{L(p,\tau,s,u,Z,Y) : p \in \mathbb R^K,\ p \ge 0,\ \tau \in \mathbb R^J\}$. Write $M_k(x) = (\xi^k-\mu(x))(\xi^k-\mu(x))^\top$. Then:
--
--   1. if $Q^k(x) - s - u^\top\xi^k - M_k(x)\bullet Y \le 0$ for all $k$ and $u + 2z_2 = 0$, the maximum of this set exists and equals
--   $$s + \Sigma(x)\bullet z_1 - \mu(x)^\top(2z_2) + \gamma z_3 + \eta\,\Sigma(x)\bullet Y;$$
--   2. otherwise the set is unbounded above.
--
--   Hence the dual problem $\min_{s,u,Z,Y}\max_{p\ge 0,\tau} L$ in (C-22) is the minimization of the displayed expression under these two constraints together with $Z \succeq 0$, $Y \succeq 0$, which after substituting $u = -2z_2$ is the inner part of (15).
--
--   **Formalization Note** The maximum is stated with `IsGreatest`, so attainment is part of the claim; "unbounded" is `¬ BddAbove`.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, pp. 38–39, proof of Theorem 3, display after (C-22)

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting

namespace DDMomentDRO.Type3

open Matrix

theorem dual_function_C22 {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) (s : ℝ) (u : Fin J → ℝ)
    (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) :
    ((∀ k, Qn x k - s - u ⬝ᵥ ξ k - frob (outerDev ξ μ x k) Y ≤ 0) ∧ u + 2 • z2 = 0 →
        IsGreatest (lagrVals Qn ξ μ Sig γ η x s u z1 z2 z3 Y)
          (s + frob (Sig x) z1 - μ x ⬝ᵥ (2 • z2) + γ * z3 + η * frob (Sig x) Y)) ∧
    (¬ ((∀ k, Qn x k - s - u ⬝ᵥ ξ k - frob (outerDev ξ μ x k) Y ≤ 0) ∧ u + 2 • z2 = 0) →
        ¬ BddAbove (lagrVals Qn ξ μ Sig γ η x s u z1 z2 z3 Y)) := by sorry

end DDMomentDRO.Type3
