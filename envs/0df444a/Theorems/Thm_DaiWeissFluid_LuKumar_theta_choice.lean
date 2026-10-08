-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_theta_choice
-- name    : DaiWeissFluid.LuKumar.theta_choice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:23:59.454642+00:00
-- url     : https://prove2.me/theorems/87884c1c-ecc9-4fc5-aba1-34a9e92a9de7
-- title:
--   Theorem 5.1 Part II — admissible Lyapunov weights
-- statement:
--   Assume positive service times, $m_1+m_4<1$, $m_2+m_3<1$, and $m_2+m_4<1$. Define
--   $$\delta_1=(1-m_1-m_4)/2,\quad\delta_2=(1-m_2-m_3)/2,\quad\delta_3=(1-m_2-m_4)/3,$$
--   $$\theta_1=1-m_4-\min\{\delta_1,\delta_3\},\qquad\theta_2=m_2+\min\{\delta_2,\delta_3\}.$$
--   All three $\delta_i$ are positive. Moreover, $m_1<\theta_1<1-m_4$, $m_2<\theta_2<1-m_3$, and $\theta_2\le\theta_1$. These are the five conditions required for the Lyapunov components in Part II.
--
--   **Formalization Note** The paper’s indices are one-based; Lean’s are zero-based. The three $\delta_i$ are computed from the source formulas, rather than supplied as independent parameters.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 128, proof of Theorem 5.1, Part II, explicit δ and θ choices

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- The explicit weights at the end of Part II of Theorem 5.1. -/
theorem theta_choice (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : m 1 + m 3 < 1) :
    let δ1 := (1 - m 0 - m 3) / 2
    let δ2 := (1 - m 1 - m 2) / 2
    let δ3 := (1 - m 1 - m 3) / 3
    let θ1 := 1 - m 3 - min δ1 δ3
    let θ2 := m 1 + min δ2 δ3
    0 < δ1 ∧ 0 < δ2 ∧ 0 < δ3 ∧
    m 0 < θ1 ∧ θ1 < 1 - m 3 ∧
    m 1 < θ2 ∧ θ2 < 1 - m 2 ∧ θ2 ≤ θ1 := by sorry

end DaiWeissFluid.LuKumar
