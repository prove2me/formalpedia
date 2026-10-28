-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_field_strength
-- name    : CoherenceTracking.Dephasing.field_strength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:28.688742+00:00
-- url     : https://prove2.me/theorems/8bc09a40-256c-4385-80a1-7c03a826052c
-- title:
--   §III.C, p. 8 — the x–y part of the control field: ω₁² + ω₂² = (γ² + ω₀²)c / (v_z(0)² − 2γct), growing monotonically on [0, t_b) for constant ω₀
-- statement:
--   Let $\gamma>0$, let $\vec v(0)$ have coherence $c=v_x(0)^2+v_y(0)^2>0$, let $t_b=v_z(0)^2/(2\gamma c)$, and let $\omega_0$ be any function. For the tracking fields $\omega_1,\omega_2$ of eqs. (41)–(42) and every $t\in[0,t_b)$,
--   $$\omega_1(t)^2+\omega_2(t)^2=\frac{(\gamma^2+\omega_0(t)^2)\,c}{v_z(0)^2-2\gamma c\,t}.$$
--
--   Moreover, when $\omega_0(t)\equiv w_0$ is constant, $t\mapsto\omega_1(t)^2+\omega_2(t)^2$ is strictly increasing on $[0,t_b)$.
--
--   This is the length in the $x$–$y$ plane of the effective field $\vec\Omega(t)=(\omega_1(t),-\omega_2(t),\omega_0(t))$; the paper adds $\omega_0^2$ to get $|\vec\Omega(t)|^2$, and describes it as "a force vector whose length in the $x-y$ plane is growing monotonically for $0\le t\le t_b$". It shows that this length grows without bound as $t\to t_b$.
--
--   **Formalization Note** The page states the display "in the simplest case of constant $\omega_0(t)$" and for $0\le t\le t_b$; the identity is pointwise and is stated for arbitrary $\omega_0$, the monotone growth for constant $\omega_0$ as on the page, both on $[0,t_b)$, since at $t_b$ the right-hand side is undefined.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 8, §III.C (display for |Ω(t)|²)

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem field_strength (γ : ℝ) (hγ : 0 < γ) (v0 : BVec) (hc : 0 < initCoherence v0) :
    (∀ (ω0 : ℝ → ℝ), ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
      trackingFields γ v0 ω0 t 1 ^ 2 + trackingFields γ v0 ω0 t 2 ^ 2 =
        (γ ^ 2 + ω0 t ^ 2) * initCoherence v0 / (v0 2 ^ 2 - 2 * γ * initCoherence v0 * t)) ∧
    (∀ w0 : ℝ, StrictMonoOn
      (fun t => trackingFields γ v0 (fun _ => w0) t 1 ^ 2 +
        trackingFields γ v0 (fun _ => w0) t 2 ^ 2)
      (Set.Ico 0 (breakdownTime γ v0))) := by sorry
end CoherenceTracking.Dephasing
