-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_support_lagrangian
-- name    : DataDrivenRO.FwdBwd.support_lagrangian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:01:51.374907+00:00
-- url     : https://prove2.me/theorems/130991e3-d842-451d-82c7-93ff2474d3e2
-- title:
--   Proof of Theorem 6, p. ec5 — Lagrangian strong duality for max_{u∈𝒰^{FB}_ε} uᵀv
-- statement:
--   Let $m_b\le m_f$ and $\bar\sigma_f,\bar\sigma_b>0$ in $\mathbb R^d$, $\varepsilon\in(0,1)$, $v\in\mathbb R^d$. For a multiplier $\lambda>0$ let
--   $$g(\lambda) = \sup\Big\{\sum_{i=1}^d v_i(y_{1i}+y_{2i}-y_{3i}) - \lambda\sum_{i=1}^d\Big(\frac{y_{2i}^2}{2\bar\sigma_{fi}^2}+\frac{y_{3i}^2}{2\bar\sigma_{bi}^2}\Big) : m_b\le y_1\le m_f,\ y_2,y_3\ge0\Big\}.$$
--   Then for every $\lambda>0$ the set over which the supremum is taken has nonempty, bounded-above image (so $g(\lambda)$ is finite), and
--   $$\delta^*(v\mid\mathcal U^{FB}_\varepsilon) = \max_{u\in\mathcal U^{FB}_\varepsilon}u^\top v = \inf_{\lambda>0}\big\{\lambda\log(1/\varepsilon) + g(\lambda)\big\}.$$
--
--   This is the Lagrangian strong-duality step of the proof of Theorem 6, which dualises the single quadratic constraint of (23).
--
--   **Formalization Note** The page minimises over $\lambda\ge0$. At $\lambda=0$ the inner supremum is $+\infty$ unless $v=0$, and the infimum over $\lambda>0$ is the same value, so the statement takes $\lambda>0$. The infimum is stated with `IsGLB`, since it need not be attained (when $v$ has no nonzero coordinate the infimum is approached as $\lambda\to0$). The support function is the published `RobustMDP.Shared.supportFunction`, a real supremum.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 6, first display, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem support_lagrangian {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    (∀ lam : ℝ, 0 < lam →
      (lagrangianValues mb mf sf sb lam v).Nonempty ∧
        BddAbove (lagrangianValues mb mf sf sb lam v)) ∧
    IsGLB
      ((fun lam : ℝ => lam * Real.log (1 / ε) + sSup (lagrangianValues mb mf sf sb lam v)) ''
        Set.Ioi 0)
      (RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) v) := by sorry

end DataDrivenRO.FwdBwd
