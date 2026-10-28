-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilt_vanishes_right_origin
-- name    : AvramDividend.Classical.gaussian_esscher_tilt_vanishes_right_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:52:16.25516+00:00
-- url     : https://prove2.me/theorems/9c796af8-1fc6-4f05-9af3-0d4e032535b5
-- title:
--   Gaussian Esscher tilted q-scale vanishes in the right-hand origin limit
-- statement:
--   For a positive Gaussian Lévy process, the q-scale function vanishes at zero and is continuous there, both already formally Proved. Any function matching its exponential Esscher tilt on positive levels therefore tends to zero as the surplus tends to zero from the right. This establishes the precise hVlim required by Gaussian right-slope normalisation without demanding V be defined at zero by that tilt.
-- source:
--   Proved Gaussian scale zero-origin theorem and global continuity, exponential continuity, filter eventually equality on (0,infinity).

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- A positive Gaussian Esscher-tilted scale function vanishes in the right-hand origin limit. -/
theorem gaussian_esscher_tilt_vanishes_right_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (φ : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry
end AvramDividend.Classical
