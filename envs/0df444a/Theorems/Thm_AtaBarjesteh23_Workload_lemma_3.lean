-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_3
-- name    : AtaBarjesteh23.Workload.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:09.899624+00:00
-- url     : https://prove2.me/theorems/56476a51-4fcc-4649-ad3d-161f6607b7e7
-- title:
--   Lemma 3, p. 19 — a solution of (43)–(45) has γ > 0, l = l_γ < 0 and u = γ/h⋆ > 0
-- statement:
--   Assume the standing assumptions. If $l<u$, $\gamma\in\mathbb R$ and $v\in C^1([l,u])$ satisfy the Riccati form of the Bellman equation
--   $$v'(w)=\frac{m'H^{-1}m}{2\sigma^2}v^2(w)-\frac{2\mu}{\sigma^2}v(w)+\frac{2(\gamma-h(w))}{\sigma^2},\quad w\in(l,u), \tag{43}$$
--   with $v(l)=-\kappa$, $v(u)=0$ (44) and $v'(l)=v'(u)=0$ (45), then $\gamma>0$ and
--   $$l=-\frac1{b^\star}\Big(\gamma+\mu\kappa+\frac{m'H^{-1}m}{4}\kappa^2\Big)<0\qquad\text{and}\qquad u=\frac{\gamma}{h^\star}>0. \tag{49}$$
--
--   Lemma 3 pins the free boundaries to $\gamma$ and splits the problem at $0$ into the two Riccati problems (50)–(53).
--
--   **Formalization Note** $l<u$ is part of the Bellman predicate (it is implicit in $C^1([l,u])$).
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 19, Lemma 3, (43)–(45), (49)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

namespace AtaBarjesteh23.Workload

theorem lemma_3 (M : Model) (hM : M.Standing) (l u γ : ℝ) (v : ℝ → ℝ)
    (hv : M.BellmanV l u γ v) :
    0 < γ ∧ l = M.lgam γ ∧ l < 0 ∧ u = M.ugam γ ∧ 0 < u := by sorry

end AtaBarjesteh23.Workload
