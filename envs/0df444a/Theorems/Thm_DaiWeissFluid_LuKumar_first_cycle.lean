-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_first_cycle
-- name    : DaiWeissFluid.LuKumar.first_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:21:33.138376+00:00
-- url     : https://prove2.me/theorems/c256f446-70e2-407c-99a7-b8d946fbeee9
-- title:
--   Theorem 5.1 Part I — first priority cycle
-- statement:
--   Suppose all four service times are positive, $m_1+m_4<1$, $m_2+m_3<1$, and $m_2+m_4\ge1$. Write $\mu_k=1/m_k$, $t_1=1/(\mu_1-1)$, $t_2=1/(\mu_2-1)$, $t_3=t_2+m_3/(1-m_2)$, and $t_4=t_2+m_4/(1-m_2)$. There is a **single** Lu–Kumar priority fluid solution starting from $(1,0,0,0)$ whose successive states are
--   $$Q(t_1)=(0,(\mu_1-\mu_2)t_1,\mu_2t_1,0),\quad Q(t_2)=(0,0,1/(1-m_2),0),$$
--   $$Q(t_3)=(t_3-t_2,0,0,(\mu_3-\mu_4)(t_3-t_2)),\quad Q(t_4)=(m_4/(1-m_2),0,0,0).$$
--   This records the complete first cycle of the priority fluid dynamics.
--
--   **Formalization Note** The paper’s class $k$ is Lean index $k-1$. No order hypotheses such as $m_1<m_2$ are added: they follow from (5.1) and (5.2).
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 126, proof of Theorem 5.1, Part I, first-cycle states

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- The four states of the first Lu–Kumar priority cycle, p. 126. -/
theorem first_cycle (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : 1 ≤ m 1 + m 3) :
    let μ1 := (m 0)⁻¹
    let μ2 := (m 1)⁻¹
    let μ3 := (m 2)⁻¹
    let μ4 := (m 3)⁻¹
    let t1 := 1 / (μ1 - 1)
    let t2 := 1 / (μ2 - 1)
    let t3 := t2 + m 2 / (1 - m 1)
    let t4 := t2 + m 3 / (1 - m 1)
    ∃ Q T, (luKumar m).IsPrioritySolution piLK Q T ∧
      Q 0 = ![1, 0, 0, 0] ∧
      Q t1 = ![0, (μ1 - μ2) * t1, μ2 * t1, 0] ∧
      Q t2 = ![0, 0, 1 / (1 - m 1), 0] ∧
      Q t3 = ![t3 - t2, 0, 0, (μ3 - μ4) * (t3 - t2)] ∧
      Q t4 = ![m 3 / (1 - m 1), 0, 0, 0] := by sorry

end DaiWeissFluid.LuKumar
