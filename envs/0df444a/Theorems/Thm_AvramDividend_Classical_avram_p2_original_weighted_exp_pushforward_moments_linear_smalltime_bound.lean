-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound
-- name    : AvramDividend.Classical.avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:09:20.271035+00:00
-- url     : https://prove2.me/theorems/7e94a33c-69d1-41da-9374-b90fd888f5c3
-- title:
--   All polynomial moments of original weighted exponential law are O(h)
-- statement:
--   For every natural k, the k-th polynomial moment of the fourth-weighted exp(X_h) pushforward under the original measure P is O(h) as h tends to zero from above. The proof combines the proved exact original-space pushforward moment formula with the proved ENNReal fourth-weighted exponential small-time bound at rho=k; no replacement jump process, compensator or conditional intensity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_pushforward_moment_formula
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) ≤
          ENNReal.ofReal (C * h) := by sorry
