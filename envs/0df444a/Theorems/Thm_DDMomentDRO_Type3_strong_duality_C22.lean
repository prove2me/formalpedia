-- Prove2me | Theorems.Thm_DDMomentDRO_Type3_strong_duality_C22
-- name    : DDMomentDRO.Type3.strong_duality_C22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:25.909699+00:00
-- url     : https://prove2.me/theorems/74ac83b5-3a07-46c4-bea9-abf2475b0032
-- title:
--   (C-22), p. 38 — under Slater, strong duality with both sides attained
-- statement:
--   Fix a state $x$ with $\Sigma(x) \succ 0$, and suppose Slater's condition holds at $x$: there is $\hat p \in \mathbb R^K$ with $\hat p \ge 0$, $\sum_k \hat p_k = 1$,
--   $$\Big(\sum_k \hat p_k\xi^k - \mu(x)\Big)^\top \Sigma(x)^{-1}\Big(\sum_k \hat p_k\xi^k - \mu(x)\Big) < \gamma, \qquad \sum_k \hat p_k M_k(x) \prec \eta\,\Sigma(x).$$
--   Then there exist $p \in \mathcal P^{D_3}(x)$ and a point $(s,z_1,z_2,z_3,Y)$ satisfying (15b)–(15c) with
--   $$\sum_{k=1}^K p_k Q^k(x) = s + \Sigma(x)\bullet z_1 - 2\mu(x)^\top z_2 + \gamma z_3 + \eta\,\Sigma(x)\bullet Y.$$
--
--   Together with weak duality this says that the inner maximum of the Bellman equation under the Type 3 set is attained and equals the attained minimum of the SDP (15a)–(15c) without the stage cost.
--
--   **Formalization Note** The page's Slater point is "a vector $p$"; it is read as a probability vector ($p \ge 0$), following Theorem A.3 ("a probability measure"), since $p \ge 0$ is part of the domain of (C-20). The inequalities are strict ($<$, `PosDef`).
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 38, proof of Theorem 3, (C-22); p. 12, Theorem 3 (Slater clause, completed from Theorem B.6, p. 36)

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting

namespace DDMomentDRO.Type3

open Matrix

theorem strong_duality_C22 {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) (hSig : (Sig x).PosDef)
    (hslater : ∃ p : Fin K → ℝ, IsSlaterPoint ξ μ Sig γ η x p) :
    ∃ p ∈ amb3 ξ μ Sig γ η x, ∃ (s : ℝ) (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ)
      (z3 : ℝ) (Y : Matrix (Fin J) (Fin J) ℝ),
      DualFeas3 Qn ξ μ x s z1 z2 z3 Y ∧
        ∑ k, p k * Qn x k = dualObj3 μ Sig γ η x s z1 z2 z3 Y := by sorry

end DDMomentDRO.Type3
