-- Prove2me | Theorems.Thm_AccelMM_BTMap_hessian_lower_bound
-- name    : AccelMM.BTMap.hessian_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:26.926932+00:00
-- url     : https://prove2.me/theorems/84c5b407-db36-42bb-a005-9b5dc715e111
-- title:
--   §4.2, p. 12 — Hessian lower bound ∇²(−ρ)(w) ⪰ c_ω L_M + e^{−ω}βI on W_ω
-- statement:
--   Let $\beta>0$, $\omega\ge0$, and $f=-\rho$. For every $w\in W_\omega$ the Hessian of $f$ dominates
--   $$A_{W_\omega}=c_\omega L_M+e^{-\omega}\beta I,\qquad c_\omega=\frac{1}{(e^{-\omega}+e^{\omega})^2},$$
--   in the positive semidefinite order: for all $v\in\mathbb R^n$,
--   $$v^\top A_{W_\omega}v\le v^\top\nabla^2f(w)\,v .$$
--
--   This is hypothesis (A1) of Lemma 4.1 for the Bradley–Terry MAP problem, and it is where the algebraic connectivity of the comparison graph enters the rate.
--
--   **Formalization Note** $v^\top\nabla^2f(w)v$ is written as the second iterated Fréchet derivative of $f$ at $w$ applied to $(v,v)$. $\beta>0$ is the standing assumption on the prior (§2).
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 12, §4.2; (7.5), p. 21

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem hessian_lower_bound {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hβ : 0 < β) (hω : 0 ≤ ω) (w : E n) (hw : w ∈ box ω) (v : E n) :
    v.ofLp ⬝ᵥ (AW d ω β).mulVec v.ofLp ≤
      iteratedFDeriv ℝ 2 (fun u => -rho α β d u) w ![v, v] := by sorry

end AccelMM.BTMap
