-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_eq_37_38
-- name    : CoherenceTracking.Dephasing.eq_37_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:27.270402+00:00
-- url     : https://prove2.me/theorems/2a4a4ee2-2c60-4775-92d4-7a7db9b9893e
-- title:
--   §III.B.2, eqs. (37)–(38), p. 6 — v_z(t) = (±)√(v_z(0)² − 2γct), so constant coherence cannot last past t_b = v_z(0)²/(2γc)
-- statement:
--   Let $\gamma>0$. Let $\vec v(t)$ solve the Bloch equations (30) on $[0,T)$ for arbitrary controls, with initial coherence $c=v_x(0)^2+v_y(0)^2>0$, and suppose the coherence is constant: $v_x(t)^2+v_y(t)^2=c$ for all $t\in[0,T)$. Then for all $t\in[0,T)$
--   $$v_z(t)=\operatorname{sign}\bigl(v_z(0)\bigr)\sqrt{v_z(0)^2-2\gamma c\,t},$$
--   and
--   $$T\le t_b=\frac{v_z(0)^2}{2\gamma c}.$$
--
--   The first display is eq. (37), with the sign $(\pm)$ identified as the sign of $v_z(0)$; the second is the content of eq. (38): $v_z$ "does not stay real for times $t>t_b$", so no trajectory of constant coherence exists on an interval longer than $t_b$. In particular, if $v_z(0)=0$ then $t_b=0$ and no such trajectory exists on any nontrivial interval.
--
--   **Formalization Note** The hypotheses $\gamma>0$ and $c>0$ are added because $t_b$ divides by $2\gamma c$ (Lean's $x/0=0$ would otherwise make $t_b=0$). The controls are arbitrary; $v_x$, $v_y$ are not assumed frozen.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 6, §III.B.2, eqs. (37)–(38)

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem eq_37_38 (γ : ℝ) (hγ : 0 < γ) (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ)
    (hv : SolvesBloch γ ω v T) (hc : 0 < initCoherence (v 0))
    (hcoh : ∀ t ∈ Set.Ico 0 T, initCoherence (v t) = initCoherence (v 0)) :
    (∀ t ∈ Set.Ico 0 T,
        v t 2 = Real.sign (v 0 2) * √(v 0 2 ^ 2 - 2 * γ * initCoherence (v 0) * t)) ∧
    T ≤ breakdownTime γ (v 0) := by sorry
end CoherenceTracking.Dephasing
