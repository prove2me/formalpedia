-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_19
-- name    : AtaBarjesteh23.Workload.lemma_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:21.728986+00:00
-- url     : https://prove2.me/theorems/f01d61c7-f23b-470a-b18b-249ec515f002
-- title:
--   Lemma 19, p. 80 — the solution of (203) has v′ > 0 (posed on every [0, w̄] where it exists)
-- statement:
--   Assume the standing assumptions and let $\bar w>0$. Let $v$ be a continuously differentiable solution on $[0,\bar w]$ of
--   $$v'(w)=\frac{m'H^{-1}m}{2\sigma^2}\big(v^2(w)-\kappa^2\big)-\frac{2\mu}{\sigma^2}\big(v(w)+\kappa\big)+\frac{2b^\star}{\sigma^2}w \tag{203}$$
--   with $v(0)=-\kappa$. Then
--   $$v'(w)>0\qquad\text{for all }w\in(0,\bar w].$$
--
--   Lemma 19 gives the monotonicity of the lower Riccati solution, used in Corollary 6 and Lemma 4.
--
--   **Formalization Note** As for Lemma 18, the paper's $[0,\infty)$ is replaced by every bounded interval $[0,\bar w]$ on which a solution exists (the solution blows up in finite time). $v'(w)$ is the derivative within $[0,\bar w]$ (one-sided at $\bar w$).
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 80, Lemma 19, (203)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem lemma_19 (M : Model) (hM : M.Standing) (wbar : ℝ) (hwbar : 0 < wbar) (v : ℝ → ℝ)
    (hv0 : v 0 = -M.kappa)
    (hode : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt v
      (M.a / (2 * M.σ ^ 2) * (v w ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (v w + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * w) (Icc 0 wbar) w) :
    ∀ w ∈ Ioc 0 wbar, 0 < derivWithin v (Icc 0 wbar) w := by sorry

end AtaBarjesteh23.Workload
