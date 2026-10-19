-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_lemma_1_informed
-- name    : FarmerInfo.Exclusive.lemma_1_informed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:54.163976+00:00
-- url     : https://prove2.me/theorems/cb639903-7753-4eb6-b157-bb692201ad01
-- title:
--   Lemma 1(1), p. 10 — posterior means for an informed farmer
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   For distinct farmers $i$ and $t$, the conditional means given $i$’s private signal and the public signal are
--
--   $$\mathbb E[u\mid x_i,y]=\mathbb E[x_t\mid x_i,y]=k_Ix_i+m_Iy,\qquad k_I=\frac{\gamma}{\alpha+\beta+\gamma},\quad m_I=\frac{\beta}{\alpha+\beta+\gamma}.$$
--
--   These posterior means are used in the informed farmer’s best response.
--
--   **Formalization Note** Conditional expectations are asserted almost surely on the product Gaussian probability space.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 10, Lemma 1(1), equation (4)

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Lemma 1(1), p. 10: informed posterior means. -/
theorem lemma_1_informed (M : Model) (hM : M.Standing) (i : Fin M.n) :
    let m : MeasurableSpace M.Ω :=
      MeasurableSpace.comap (fun ω : M.Ω => (M.x i ω, M.y ω)) inferInstance
    (M.P[fun ω : M.Ω => M.u ω | m] =ᵐ[M.P]
      fun ω : M.Ω => M.kI * M.x i ω + M.mI * M.y ω) ∧
    (∀ t : Fin M.n, t ≠ i →
      M.P[fun ω : M.Ω => M.x t ω | m] =ᵐ[M.P]
        fun ω : M.Ω => M.kI * M.x i ω + M.mI * M.y ω) := by sorry
end
end FarmerInfo.Exclusive
