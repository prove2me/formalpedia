-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_lemma_2
-- name    : FarmerInfo.Exclusive.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:47.292035+00:00
-- url     : https://prove2.me/theorems/358f10a5-8dda-4de0-b12b-bb8b9070eca3
-- title:
--   Lemma 2, p. 14 — informed and uninformed expected profit
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   At the linear equilibrium, each informed farmer earns $W^I(n_1,\beta;\gamma)$, each uninformed farmer earns $W^J(n_1,\beta;\gamma)$, with the displayed quadratic formulas of Lemma 2, and
--
--   $$W^I(n_1,\beta;\gamma)>W^J(n_1,\beta;\gamma)$$
--
--   when both groups contain a farmer. This links realized game profits to the planner’s closed-form welfare function.
--
--   **Formalization Note** The strict comparison is asserted only when both types of farmer exist; positive public precision is part of the standing assumptions.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 14, Lemma 2

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Lemma 2, p. 14: the two ex-ante profit formulas and their strict comparison. -/
theorem lemma_2 (M : Model) (hM : M.Standing) :
    ∀ I : Finset (Fin M.n),
      (∀ i : Fin M.n, i ∈ I →
        (∫ ω, M.profit I (M.linProfile I) i ω ∂M.P) = M.WI (I.card : ℝ)) ∧
      (∀ j : Fin M.n, j ∉ I →
        (∫ ω, M.profit I (M.linProfile I) j ω ∂M.P) = M.WJ (I.card : ℝ)) ∧
      (I.Nonempty → (Finset.univ \ I).Nonempty →
        M.WJ (I.card : ℝ) < M.WI (I.card : ℝ)) := by sorry
end
end FarmerInfo.Exclusive
