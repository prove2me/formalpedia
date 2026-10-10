-- Prove2me | Theorems.Thm_DDMomentDRO_Type3_weak_duality_C22
-- name    : DDMomentDRO.Type3.weak_duality_C22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:20.236131+00:00
-- url     : https://prove2.me/theorems/9f5a235e-e573-4ca6-85ad-be5f52eedcdb
-- title:
--   (C-22), p. 38, weak half — every p in the Type 3 set is bounded by every feasible point of (15b)–(15c)
-- statement:
--   Fix a state $x$ with $\Sigma(x) \succ 0$. Let $p$ belong to the Type 3 ambiguity set $\mathcal P^{D_3}(x)$ of (14) (with $p \ge 0$), and let $(s,z_1,z_2,z_3,Y)$ satisfy (15b)–(15c): $Z = \begin{pmatrix} z_1 & z_2\\ z_2^\top & z_3\end{pmatrix}\succeq 0$, $Y \succeq 0$ and $s - 2z_2^\top\xi^k + M_k(x)\bullet Y \ge Q^k(x)$ for all $k$. Then
--   $$\sum_{k=1}^K p_k Q^k(x) \le s + \Sigma(x)\bullet z_1 - 2\mu(x)^\top z_2 + \gamma z_3 + \eta\,\Sigma(x)\bullet Y.$$
--
--   This is the "max ≤ min" half of the duality (C-22) between the inner problem of the Bellman equation and the SDP (15) without the stage cost.
--
--   **Formalization Note** $\Sigma(x) \succ 0$ is implicit on the page and needed for the inverse in (14b) to be the true inverse.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 38, proof of Theorem 3, (C-22)

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting

namespace DDMomentDRO.Type3

open Matrix

theorem weak_duality_C22 {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) (hSig : (Sig x).PosDef)
    (p : Fin K → ℝ) (hp : p ∈ amb3 ξ μ Sig γ η x)
    (s : ℝ) (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) (hd : DualFeas3 Qn ξ μ x s z1 z2 z3 Y) :
    ∑ k, p k * Qn x k ≤ dualObj3 μ Sig γ η x s z1 z2 z3 Y := by sorry

end DDMomentDRO.Type3
