-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_eq_41_42
-- name    : CoherenceTracking.Dephasing.eq_41_42
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:26.943718+00:00
-- url     : https://prove2.me/theorems/b2df7023-d350-447e-93a0-d28c4c7ed1b0
-- title:
--   §III.B.2, eqs. (41)–(42), p. 6 — the fields that freeze v_x, v_y solve the Bloch equations until t_b, and are the only ones
-- statement:
--   Let $\gamma>0$, and let $\vec v(0)$ be a vector with $v_z(0)\ne0$ and coherence $c=v_x(0)^2+v_y(0)^2>0$. Put $s=\operatorname{sign}v_z(0)$, $R(t)=v_z(0)^2-2\gamma ct$, $t_b=v_z(0)^2/(2\gamma c)$, and
--   $$\vec v(t)=\bigl(v_x(0),\,v_y(0),\,s\sqrt{R(t)}\bigr).$$
--   For an arbitrary function $\omega_0$ define
--   $$\omega_2(t)=s\,\frac{-\gamma v_x(0)-\omega_0(t)v_y(0)}{\sqrt{R(t)}},\qquad \omega_1(t)=s\,\frac{-\gamma v_y(0)+\omega_0(t)v_x(0)}{\sqrt{R(t)}} .$$
--   Then:
--
--   1. $\vec v(t)$ equals $\vec v(0)$ at $t=0$;
--   2. for every $\omega_0$ and every $t\in[0,t_b)$, $\vec v$ is differentiable at $t$ and satisfies the Bloch equations (30) with the controls $(\omega_0,\omega_1,\omega_2)$;
--   3. conversely, if at some $t\in[0,t_b)$ the curve $\vec v$ satisfies (30) with controls $(\omega_0(t),\omega_1(t),\omega_2(t))$, then $\omega_1(t)$ and $\omega_2(t)$ are given by the formulas above.
--
--   These are eqs. (41)–(42): keeping $v_x$ and $v_y$ fixed — a linearization of the constraint of constant coherence — forces exactly these fields, and $\omega_0$ may be chosen freely.
--
--   **Formalization Note** The sign $(\pm)$ is $\operatorname{sign}v_z(0)$. All conclusions are restricted to $[0,t_b)$, where $R(t)>0$ and the square root is the paper's. The hypothesis $c>0$ is added for the definition of $t_b$.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 6, §III.B.2, eqs. (41)–(42)

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem eq_41_42 (γ : ℝ) (hγ : 0 < γ) (v0 : BVec) (hz : v0 2 ≠ 0) (hc : 0 < initCoherence v0) :
    trackedBloch γ v0 0 = v0 ∧
    (∀ ω0 : ℝ → ℝ, ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
        HasDerivAt (trackedBloch γ v0)
          ((blochMatrix γ (trackingFields γ v0 ω0 t)).mulVec (trackedBloch γ v0 t)) t) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ), ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
        HasDerivAt (trackedBloch γ v0) ((blochMatrix γ (ω t)).mulVec (trackedBloch γ v0 t)) t →
        ω t 1 = trackingFields γ v0 (fun s => ω s 0) t 1 ∧
        ω t 2 = trackingFields γ v0 (fun s => ω s 0) t 2) := by sorry
end CoherenceTracking.Dephasing
