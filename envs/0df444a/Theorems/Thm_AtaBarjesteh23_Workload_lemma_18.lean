-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_18
-- name    : AtaBarjesteh23.Workload.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:13.33519+00:00
-- url     : https://prove2.me/theorems/d6021518-cf94-46b7-98f8-99536290955e
-- title:
--   Lemma 18, p. 80 — the shifted lower Riccati solution of (202) stays ≥ −κ (posed on every [0, w̄] where it exists)
-- statement:
--   Assume the standing assumptions and let $\bar w>0$. Let $v$ be a continuously differentiable solution on $[0,\bar w]$ of
--   $$v'(w)=\frac{m'H^{-1}m}{2\sigma^2}\big(v^2(w)-\kappa^2\big)-\frac{2\mu}{\sigma^2}\big(v(w)+\kappa\big)+\frac{2b^\star}{\sigma^2}w \tag{202}$$
--   with $v(0)=-\kappa$. Then
--   $$v(w)\ge-\kappa\qquad\text{for all }w\in[0,\bar w].$$
--
--   Lemma 18 is the lower bound used in the proof of Lemma 19.
--
--   **Formalization Note** The paper states the lemma for a solution on $[0,\infty)$. No such solution exists: the quadratic term forces finite-time blow-up, so the printed statement would be vacuous. The lemma is posed on every bounded interval $[0,\bar w]$ on which a solution exists; the printed proof is local and applies unchanged. The equation is required at every point of $[0,\bar w]$, with one-sided derivatives at the ends, which makes $v$ continuously differentiable up to the boundary.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 80, Lemma 18, (202)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem lemma_18 (M : Model) (hM : M.Standing) (wbar : ℝ) (hwbar : 0 < wbar) (v : ℝ → ℝ)
    (hv0 : v 0 = -M.kappa)
    (hode : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt v
      (M.a / (2 * M.σ ^ 2) * (v w ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (v w + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * w) (Icc 0 wbar) w) :
    ∀ w ∈ Icc 0 wbar, -M.kappa ≤ v w := by sorry

end AtaBarjesteh23.Workload
