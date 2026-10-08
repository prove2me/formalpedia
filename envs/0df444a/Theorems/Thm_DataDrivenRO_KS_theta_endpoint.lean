-- Prove2me | Theorems.Thm_DataDrivenRO_KS_theta_endpoint
-- name    : DataDrivenRO.KS.theta_endpoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:41.385985+00:00
-- url     : https://prove2.me/theorems/b95d1723-0226-49dd-b993-5c5b73176ad0
-- title:
--   (EC.7), p. ec4 — the linear optimization over θᵢ ∈ [0,1] attains its maximum at θᵢ = 0 or θᵢ = 1
-- statement:
--   Let $w\in\mathbb R^{N+2}$. The function
--   $$\theta\mapsto\sum_{j=0}^{N+1}\big(\theta q^L_j(\Gamma)+(1-\theta)q^R_j(\Gamma)\big)w_j$$
--   attains its maximum over $\theta\in[0,1]$, and that maximum equals
--   $$\max\Big(\sum_{j=0}^{N+1}q^L_j(\Gamma)w_j,\ \sum_{j=0}^{N+1}q^R_j(\Gamma)w_j\Big),$$
--   its values at $\theta=1$ and $\theta=0$.
--
--   With $w_j=e^{v_i\hat u^{(j)}_i/\lambda}$ this is the step from (EC.7) to the expression (19): the inner optimizations over $\theta_i$ are linear, hence solved at an end point.
--
--   **Formalization Note** Stated as `IsGreatest` of the image of $[0,1]$; no sign condition on $w$ is needed.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 5, (EC.7) and the sentence after it, p. ec4

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem theta_endpoint (N : ℕ) (Γ : ℝ) (w : Fin (N + 2) → ℝ) :
    IsGreatest ((fun θ : ℝ => ∑ j, mix N Γ θ j * w j) '' Set.Icc 0 1)
      (max (∑ j, qL N Γ j * w j) (∑ j, qR N Γ j * w j)) := by sorry

end DataDrivenRO.KS
