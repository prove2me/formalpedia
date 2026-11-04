-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightjump_residual_summable_of_cash_mass_majorant
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_rightjump_residual_summable_of_cash_mass_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:28:25.467191+00:00
-- url     : https://prove2.me/theorems/571a56e3-3d61-4d7d-be6f-29157d9106b3
-- title:
--   Source Cash right-jump summability controls every norm-dominated original signed correction
-- statement:
--   For the true original dividend strategy on any set of nonnegative payment times, summability of the actual right-limit cash jump series and an explicit pointwise norm domination by K times each original cash jump imply summability of the proposed signed Itô remainder. This isolates the missing local Lipschitz or secant bound required to apply the countable jump sign theorem.
-- source:
--   True original rightLimit D t ω jump mass, Mathlib Summable.of_norm_bounded and Summable.const_mul, canonical source signed HJB jump remainder.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_rightjump_residual_summable_of_cash_mass_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (A : Set ℝ≥0)
    (R : A → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hCash : Summable (fun a : A =>
      rightLimit D a.1 ω - D a.1 ω))
    (hMajor : ∀ a : A, ‖R a‖ ≤
      K * (rightLimit D a.1 ω - D a.1 ω)) :
    Summable R := by sorry
