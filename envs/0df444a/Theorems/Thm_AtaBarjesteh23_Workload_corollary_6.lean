-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_corollary_6
-- name    : AtaBarjesteh23.Workload.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:06.431636+00:00
-- url     : https://prove2.me/theorems/658ed95a-df92-4a5f-8e86-530dd799105f
-- title:
--   Corollary 6, p. 82 — for l < 0 the lower Riccati solution on [l, 0] with v(l) = −κ has v′ > 0 on (l, 0]
-- statement:
--   Assume the standing assumptions and let $l<0$. Let $v\in C^1([l,0])$ solve
--   $$v'(w)=\frac{m'H^{-1}m}{2\sigma^2}\big(v^2(w)-\kappa^2\big)-\frac{2\mu}{\sigma^2}\big(v(w)+\kappa\big)+\frac{2(h(l)-h(w))}{\sigma^2}$$
--   with $v(l)=-\kappa$. Then
--   $$v'(w)>0\qquad\text{for all }w\in(l,0].$$
--
--   This is the monotonicity of $v^-_\gamma$ (take $l=l_\gamma$), used in Lemma 4 and Proposition 3.
--
--   **Formalization Note** The equation is required on the closed interval $[l,0]$ with one-sided derivatives at the ends; for a $C^1$ solution on $(l,0)$ this is equivalent, by continuity. $v'(w)$ is the derivative within $[l,0]$ (one-sided at $0$).
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 82, Corollary 6

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem corollary_6 (M : Model) (hM : M.Standing) (l : ℝ) (hl : l < 0) (v : ℝ → ℝ)
    (hvl : v l = -M.kappa)
    (hode : ∀ w ∈ Icc l 0, HasDerivWithinAt v (M.rhsLower l w (v w)) (Icc l 0) w) :
    ∀ w ∈ Ioc l 0, 0 < derivWithin v (Icc l 0) w := by sorry

end AtaBarjesteh23.Workload
