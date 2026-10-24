-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_20
-- name    : AtaBarjesteh23.Workload.lemma_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:17.045492+00:00
-- url     : https://prove2.me/theorems/f851d8fe-d4a7-4936-bbd0-d892b99dbd56
-- title:
--   Lemma 20, p. 82 — the solution of (211) has v, v′ < 0 (posed on every [0, w̄] where it exists)
-- statement:
--   Assume the standing assumptions and let $\bar w>0$. Let $v$ be a continuously differentiable solution on $[0,\bar w]$ of
--   $$v'(w)=-\frac{m'H^{-1}m}{2\sigma^2}v^2(w)+\frac{2\mu}{\sigma^2}v(w)-\frac{2h^\star}{\sigma^2}w \tag{211}$$
--   with $v(0)=0$. Then
--   $$v(w)<0\quad\text{and}\quad v'(w)<0\qquad\text{for all }w\in(0,\bar w].$$
--
--   Reflected through $w\mapsto u_\gamma-w$, this gives the sign and monotonicity of the upper Riccati solution $v^+_\gamma$.
--
--   **Formalization Note** The paper states the lemma on $[0,\infty)$, where no solution exists (with $\mu\ge0$, the solution tends to $-\infty$ in finite time); it is posed on every bounded interval $[0,\bar w]$ on which a solution exists. The proof uses $\mu\ge0$, a standing assumption.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 82, Lemma 20, (211)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem lemma_20 (M : Model) (hM : M.Standing) (wbar : ℝ) (hwbar : 0 < wbar) (v : ℝ → ℝ)
    (hv0 : v 0 = 0)
    (hode : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt v
      (-(M.a / (2 * M.σ ^ 2)) * v w ^ 2 + 2 * M.μ / M.σ ^ 2 * v w - 2 * M.hStar / M.σ ^ 2 * w)
      (Icc 0 wbar) w) :
    ∀ w ∈ Ioc 0 wbar, v w < 0 ∧ derivWithin v (Icc 0 wbar) w < 0 := by sorry

end AtaBarjesteh23.Workload
