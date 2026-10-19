-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_lemma_1_uninformed
-- name    : FarmerInfo.Exclusive.lemma_1_uninformed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:53.919466+00:00
-- url     : https://prove2.me/theorems/a44a5066-05c6-4852-8b0f-5222e35e85c5
-- title:
--   Lemma 1(2), p. 10 — posterior means for an uninformed farmer
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   For distinct farmers $j$ and $t$, a farmer without the public signal has
--
--   $$\mathbb E[u\mid x_j]=\mathbb E[x_t\mid x_j]=\mathbb E[y\mid x_j]=k_Jx_j,\qquad k_J=\frac{\gamma}{\alpha+\gamma}.$$
--
--   This gives the uninformed farmer’s posterior beliefs using only its private signal.
--
--   **Formalization Note** The three conditional-expectation identities hold almost surely under the product Gaussian law.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 10, Lemma 1(2)

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Lemma 1(2), p. 10: uninformed posterior means. -/
theorem lemma_1_uninformed (M : Model) (hM : M.Standing) (j : Fin M.n) :
    let m : MeasurableSpace M.Ω := MeasurableSpace.comap (M.x j) inferInstance
    (M.P[fun ω : M.Ω => M.u ω | m] =ᵐ[M.P]
      fun ω : M.Ω => M.kJ * M.x j ω) ∧
    (∀ t : Fin M.n, t ≠ j →
      M.P[fun ω : M.Ω => M.x t ω | m] =ᵐ[M.P]
        fun ω : M.Ω => M.kJ * M.x j ω) ∧
    (M.P[fun ω : M.Ω => M.y ω | m] =ᵐ[M.P]
      fun ω : M.Ω => M.kJ * M.x j ω) := by sorry
end
end FarmerInfo.Exclusive
