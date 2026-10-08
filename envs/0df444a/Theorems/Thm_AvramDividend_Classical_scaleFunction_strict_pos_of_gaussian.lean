-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:51:17.767189+00:00
-- url     : https://prove2.me/theorems/20a6eb76-1c62-4441-957b-0ec1e50b7651
-- title:
--   A canonical q-scale function is strictly positive in the Gaussian branch
-- statement:
--   If the spectrally negative Lévy process has a nonzero Gaussian coefficient, then every q-scale function in the exact Avram framework is strictly positive at every positive capital level. The result uses the Lévy measure's built-in moment condition to eliminate an extra jump-integrability hypothesis.
-- source:
--   Composition of accepted psi_quadratic_upper, psi_eventually_gt_of_gaussian_levy_integrable, scaleFunction_strict_pos_of_eventual_psi_bound, and newly requested source-faithful levy_compensated_jump_integrable_nonneg. Handles the Gaussian disjunct of Condition33; non-Gaussian Standing branches remain open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaleFunction_strict_pos_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (a : ℝ) (ha : 0 < a) :
    0 < W a := by sorry
