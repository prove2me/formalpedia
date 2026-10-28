-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_eq_36
-- name    : CoherenceTracking.Dephasing.eq_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:32.542512+00:00
-- url     : https://prove2.me/theorems/d73713bf-740d-42a1-970a-4e2c8b14e797
-- title:
--   §III.B.2, eq. (36), p. 6 — under constant coherence c, v̇_z(t) = −γc / v_z(t)
-- statement:
--   Let $\gamma>0$ and $c>0$. Let $\vec v(t)=(v_x,v_y,v_z)(t)$ solve the Bloch equations (30) on $[0,T)$ for arbitrary controls $\omega_0,\omega_1,\omega_2$, and suppose the coherence stays constant, $v_x(t)^2+v_y(t)^2=c$ for all $t\in[0,T)$. Then for every $t\in(0,T)$ the $z$-component does not vanish and
--   $$\dot v_z(t)=\frac{-\gamma c}{v_z(t)} .$$
--
--   This is eq. (36): the constraint of constant coherence alone, for any choice of controls, fixes the motion of $v_z$.
--
--   **Formalization Note** The hypotheses $\gamma>0$ and $c>0$ are added because the paper divides by $v_z$ and later by $2\gamma c$; under them $v_z(t)\ne0$ is part of the conclusion, so the division in (36) is never Lean's $x/0=0$.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 6, §III.B.2, eq. (36)

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem eq_36 (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ)
    (hv : SolvesBloch γ ω v T) (hcoh : ∀ t ∈ Set.Ico 0 T, v t 0 ^ 2 + v t 1 ^ 2 = c) :
    ∀ t ∈ Set.Ioo 0 T, v t 2 ≠ 0 ∧ HasDerivAt (fun s => v s 2) (-(γ * c) / v t 2) t := by sorry
end CoherenceTracking.Dephasing
