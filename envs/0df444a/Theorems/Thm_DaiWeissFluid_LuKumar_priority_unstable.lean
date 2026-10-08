-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_priority_unstable
-- name    : DaiWeissFluid.LuKumar.priority_unstable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:23:33.18098+00:00
-- url     : https://prove2.me/theorems/1232dbc4-6bcb-4a7c-a4ff-7d826a6d601a
-- title:
--   Theorem 5.1 Part I — Lu–Kumar priority instability
-- statement:
--   For positive service times satisfying $m_1+m_4<1$ and $m_2+m_3<1$, if $m_2+m_4\ge1$, the Lu–Kumar priority fluid model is unstable in the sense of Definition 1.3:
--   $$\neg\operatorname{FluidStable}(\text{Lu–Kumar priority model}).$$
--   The threshold includes equality, where the paper exhibits a periodic nonempty fluid solution.
--
--   **Formalization Note** Instability is the negation of the uniform finite-time stability definition, rather than a claim that every solution diverges. Classes are zero-based in Lean.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 127, proof of Theorem 5.1, Part I, paragraph after the scaled-cycle display

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- The unstable priority fluid model in Part I of Theorem 5.1. -/
theorem priority_unstable (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : 1 ≤ m 1 + m 3) :
    ¬ DaiWeissFluid.ThreeBuffer.FluidStable ((luKumar m).IsPrioritySolution piLK) := by sorry

end DaiWeissFluid.LuKumar
