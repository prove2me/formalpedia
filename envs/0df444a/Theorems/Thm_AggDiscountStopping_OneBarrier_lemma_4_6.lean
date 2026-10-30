-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_lemma_4_6
-- name    : AggDiscountStopping.OneBarrier.lemma_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:03.037988+00:00
-- url     : https://prove2.me/theorems/381a60bd-256a-47ac-bca6-7d27a35038be
-- title:
--   Lemma 4.6, p. 12 — under C-(ii)-1, m̃_r(x) < ϕ₁(x) for all x > 0
-- statement:
--   Assume the standing assumptions of §4 and Conditions C-(i) and C-(ii)-1. Fix $r\ge0$ and let $\psi$ be a positive, decreasing, $C^2$ solution on $(0,\infty)$ of
--   $$\tfrac12\sigma^2(x)\psi''(x)+\mu(x)\psi'(x)=r\psi(x).$$
--   Put $\tilde m_r(x)=-\psi'(x)/\psi(x)$. Then for every $x>0$,
--   $$\tilde m_r(x)<\phi_1(x)=\frac{\mu(x)+\sqrt{\mu^2(x)+2r\sigma^2(x)}}{\sigma^2(x)}.$$
--
--   The function $\tilde m_r$ solves the Riccati equation (4.3), $\tilde m_r'=(\tilde m_r-\phi_1)(\tilde m_r-\phi_2)$, whose larger root is $\phi_1$; the lemma says $\tilde m_r$ stays strictly below that root, which is what makes $\tilde m_r$ decreasing (Proposition 4.4).
--
--   **Formalization Note** The lemma is posed for an arbitrary positive decreasing $C^2$ solution $\psi$ of (4.1), which is how the paper uses $\varphi_r$; no process appears. C-(i) ($\mu\ge0$ on $[0,\infty)$) is a standing condition of §4 ("imposed in this section", p. 9) and is listed explicitly; the proof's boundedness of $1/\sigma^2$ at infinity uses it.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, Lemma 4.6, p. 12 (m̃_r from (4.3), p. 11)

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem lemma_4_6 (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (r : ℝ) (hr : 0 ≤ r) (ψ : ℝ → ℝ) (hψ : IsDecreasingSolution M r ψ) :
    ∀ x, 0 < x → mtilde ψ x < M.phi1 r x := by sorry

end AggDiscountStopping.OneBarrier
