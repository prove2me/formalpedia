-- Prove2me | Theorems.Thm_ClosedLoopBass_Immediate_if_plan_bass
-- name    : ClosedLoopBass.Immediate.if_plan_bass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:16.046185+00:00
-- url     : https://prove2.me/theorems/442e7c63-7c66-4b13-8d49-bfe512981f70
-- title:
--   §4.1, p. 7 — the immediate-fulfillment plan is feasible and reproduces the original Bass process: s̃ₜ = d̃ₜ, r̃ₜ = min{ẽₜ, γ₂d̃ₜ}, S̃ₜ = D̃ₜ
-- statement:
--   Consider the closed-loop sales-planning model under its standing assumptions. Let $(\widetilde n,\widetilde r)$ be the **immediate-fulfillment plan**, with $\widetilde r_t=\min\{\widetilde e_t,\gamma_2\widetilde d_t\}$ and $\widetilde n_t=\widetilde d_t-\widetilde r_t$, where $\widetilde d_t$ is the demand of the original Bass process and $\widetilde e_t$ its accumulated return volume.
--
--   Then $(\widetilde n,\widetilde r)$ is a feasible plan, i.e. it satisfies (2), (3) and (5) in every period $t=1,\dots,T$. Moreover, when this plan is run through the model (1)–(6), the following hold in every period $t\ge1$:
--
--   1. its sales meet the diffusion demand, $s_t=d_t$, and that demand is the Bass demand, $d_t=\widetilde d_t$;
--   2. its cumulative sales equal its cumulative diffusion demand, which is the Bass trajectory:
--   $$
--   S_t=D_t=\widetilde D_t;
--   $$
--   3. its backlogs vanish, $b_{1t}=b_{2t}=0$;
--   4. its return volume $e_t$ from (6) equals $\widetilde e_t$, and $\widetilde r_t=\min\{e_t,\gamma_2 d_t\}$.
--
--   This is the paper's observation that the immediate-fulfillment policy corresponds to the original Bass diffusion process. It identifies the benchmark plan of §4.1 with a feasible point of the producer's problem.
--
--   **Formalization Note** The plan is defined by an explicit recursion, not as "some plan meeting all demand". The identities are stated for every period $t\ge1$, as on the page ("$\forall t$"). Feasibility is required only for $t=1,\dots,T$.
-- source:
--   Nadar, Kaya and Güler, New-Product Diffusion in Closed-Loop Supply Chains, MSOM (Articles in Advance, 2020), doi:10.1287/msom.2019.0864, p. 7, §4.1 ("Note that s̃t = d̃t, r̃t = min{ẽt, γ2d̃t}, and S̃t = D̃t, ∀t.")

import Mathlib
import Definitions.Def_ClosedLoopBass_Immediate_Model

namespace ClosedLoopBass.Immediate

/-- §4.1, p. 7: the immediate-fulfillment plan `(ñ, r̃)` is feasible and, run through the model
(1)–(6), reproduces the original Bass process: in every period `t ≥ 1` its sales equal its
diffusion demand and `d̃_t`, its cumulative sales and cumulative diffusion demand equal `D̃_t`,
its backlogs vanish, and its remanufactured sales are `min{e_t, γ2 d_t}`. -/
theorem if_plan_bass (P : Params) (hP : Standing P) :
    Feasible P (nIF P) (rIF P) ∧
    ∀ t : ℕ, 1 ≤ t →
      sales (nIF P) (rIF P) t = d P (nIF P) (rIF P) t ∧
      d P (nIF P) (rIF P) t = dB P t ∧
      S (nIF P) (rIF P) t = D P (nIF P) (rIF P) t ∧
      D P (nIF P) (rIF P) t = DB P t ∧
      b1 P (nIF P) (rIF P) t = 0 ∧ b2 P (nIF P) (rIF P) t = 0 ∧
      e P (nIF P) (rIF P) t = eIF P t ∧
      rIF P t = min (e P (nIF P) (rIF P) t) (P.gamma2 * d P (nIF P) (rIF P) t) := by sorry

end ClosedLoopBass.Immediate
