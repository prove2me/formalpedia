-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_remark_9
-- name    : DataDrivenRO.FwdBwd.remark_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:02:47.350259+00:00
-- url     : https://prove2.me/theorems/1668d8da-f59e-4f69-b1cc-2e847cfe48a0
-- title:
--   Remark 9, p. 19 — closed-form separation: if (24) exceeds t, the point u built from λ lies in 𝒰^{FB}_ε and violates uᵀv ≤ t
-- statement:
--   Let $m_b\le m_f$ and $\bar\sigma_f,\bar\sigma_b>0$ in $\mathbb R^d$, $\varepsilon\in(0,1)$, $v\in\mathbb R^d$ with $v\neq0$, and $t\in\mathbb R$ with $\delta^*(v\mid\mathcal U^{FB}_\varepsilon)>t$, i.e. $t$ is below the right-hand side of (24). Put
--   $$\lambda = \sqrt{\frac{\sum_{i:v_i>0}v_i^2\bar\sigma_{fi}^2+\sum_{i:v_i\le0}v_i^2\bar\sigma_{bi}^2}{2\log(1/\varepsilon)}},\qquad u_i = \begin{cases} m_{fi}+\dfrac{v_i\bar\sigma_{fi}^2}{\lambda} & v_i>0,\\[4pt] m_{bi}+\dfrac{v_i\bar\sigma_{bi}^2}{\lambda} & \text{otherwise.}\end{cases}$$
--   Then $u\in\mathcal U^{FB}_\varepsilon$ and $u^\top v>t$: the inequality $u^\top v\le t$ is a valid constraint for the robust problem that the current point $(v,t)$ violates.
--
--   This gives a closed-form separation oracle for the constraint $\delta^*(v\mid\mathcal U^{FB}_\varepsilon)\le t$.
--
--   **Formalization Note** The hypothesis "$\delta^*(v\mid\mathcal U^{FB}_\varepsilon)>t$" is written with the right-hand side of (24), equal to $\delta^*$ by Theorem 6. The hypothesis $v\neq0$ is added: with $\bar\sigma>0$ it is exactly the case $\lambda>0$, where the page's formula for $u$ is defined.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Remark 9, p. 19; proof of Theorem 6, last sentence, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem remark_9 {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) (hv : v ≠ 0) (t : ℝ) (ht : t < fbValue mb mf sf sb ε v) :
    let lam : ℝ := Real.sqrt ((∑ i, if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2) /
      (2 * Real.log (1 / ε)))
    let u : Fin d → ℝ := fun i =>
      if 0 < v i then mf i + v i * sf i ^ 2 / lam else mb i + v i * sb i ^ 2 / lam
    u ∈ UFB mb mf sf sb ε ∧ t < u ⬝ᵥ v := by sorry

end DataDrivenRO.FwdBwd
