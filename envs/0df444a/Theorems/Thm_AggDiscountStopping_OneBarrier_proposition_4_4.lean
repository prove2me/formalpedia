-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_proposition_4_4
-- name    : AggDiscountStopping.OneBarrier.proposition_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:00.697974+00:00
-- url     : https://prove2.me/theorems/88cd824b-9201-4a4e-aa56-ce893e6de67b
-- title:
--   Proposition 4.4, p. 11 — under C-(ii)-1, x ↦ m̃_r(x) = −φ′_r(x)/φ_r(x) is decreasing on (0, ∞)
-- statement:
--   Assume the standing assumptions of §4 and Conditions C-(i) and C-(ii)-1. Fix $r\ge0$ and let $\psi$ be a positive, decreasing, $C^2$ solution on $(0,\infty)$ of (4.1), $\tfrac12\sigma^2\psi''+\mu\psi'=r\psi$. Then the function
--   $$x\longmapsto\tilde m_r(x)=-\frac{\psi'(x)}{\psi(x)}$$
--   is decreasing (non-increasing) on $(0,\infty)$.
--
--   Equivalently, $m_r=\psi'/\psi$ is increasing, which is condition (a″) of Remark 4.3; through $H(r,a,x)=\ln\varphi_r(x)-\ln\varphi_r(a)$ it is Condition (a) of Proposition 4.2. It makes the function $G$ of (4.8) increasing.
--
--   **Formalization Note** Condition (a) is posed in its (a″) form, as the paper's proof does ("it suffices to justify that $x\mapsto\tilde m_r(x)$ decreasing"), for an arbitrary positive decreasing $C^2$ solution. The domain is $(0,\infty)$ rather than $[0,K]$, since $\varphi_r(0)$ may be $+\infty$. C-(i) is the standing condition of §4.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, Proposition 4.4, p. 11 (with (a′′) of Remark 4.3 and (4.3))

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem proposition_4_4 (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (r : ℝ) (hr : 0 ≤ r) (ψ : ℝ → ℝ) (hψ : IsDecreasingSolution M r ψ) :
    AntitoneOn (mtilde ψ) (Ioi 0) := by sorry

end AggDiscountStopping.OneBarrier
