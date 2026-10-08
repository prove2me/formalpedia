-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_theorem5_1
-- name    : DaiWeissFluid.LuKumar.theorem5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:25:05.094988+00:00
-- url     : https://prove2.me/theorems/10593429-f088-4a31-8d40-f3003ce14ad8
-- title:
--   Theorem 5.1 — exact Lu–Kumar fluid stability region
-- statement:
--   Let the four mean service times be positive and satisfy the nominal-load conditions
--   $$m_1+m_4<1,\qquad m_2+m_3<1.$$
--   Then an unstable work-conserving fluid model exists exactly when $m_2+m_4\ge1$. Moreover, the named Lu–Kumar priority fluid model is unstable exactly in that same region:
--   $$\neg\operatorname{FluidStable}(\text{all work-conserving solutions})\iff m_2+m_4\ge1,$$
--   $$\neg\operatorname{FluidStable}(\text{Lu–Kumar priority solutions})\iff m_2+m_4\ge1.$$
--   The second equivalence records the characterization in Remark 1; together the two clauses state the paper’s exact fluid-model threshold, including equality.
--
--   **Formalization Note** “Unstable” negates Definition 1.3. A queueing policy is represented through its fluid-solution predicate. The all-work-conserving predicate includes every work-conserving discipline; the named priority predicate gives the Part I witness. Classes are numbered from zero in Lean, so the criterion is `1 ≤ m 1 + m 3`.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 125, Theorem 5.1, (5.1)–(5.2), Remark 1; pp. 126–128, proof

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- Theorem 5.1 and Remark 1, including the boundary case `m₂ + m₄ = 1`. -/
theorem theorem5_1 (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1) :
    (¬ DaiWeissFluid.ThreeBuffer.FluidStable (luKumar m).IsWorkConserving ↔ 1 ≤ m 1 + m 3) ∧
    (¬ DaiWeissFluid.ThreeBuffer.FluidStable ((luKumar m).IsPrioritySolution piLK) ↔ 1 ≤ m 1 + m 3) := by sorry

end DaiWeissFluid.LuKumar
