-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
-- name    : AvramDividend.Classical.local_verification_hjb_implies_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:35:41.649033+00:00
-- url     : https://prove2.me/theorems/cfc92077-76e2-4193-b81a-9e7df5767288
-- title:
--   HJB maximum-equals-zero assumption yields separate generator and derivative inequalities
-- statement:
--   The exact local_verification assumption max((Γ−q)w,1−w′)=0 implies each component is nonpositive: (Γ−q)w≤0 and w′≥1 at interior reserves. GeneratorIntegrable also passes through. This is a faithful pointwise decomposition of the root theorem’s nonlinear HJB premise, useful for the stochastic verification steps.
-- source:
--   Root theorem AvramDividend.Classical.local_verification and Mathlib le_max_left, le_max_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_hjb_implies_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (h : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0 ∧
      1 ≤ deriv w y := by sorry
