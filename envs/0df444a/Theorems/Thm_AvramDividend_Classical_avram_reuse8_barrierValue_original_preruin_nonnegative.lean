-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_reuse8_barrierValue_original_preruin_nonnegative
-- name    : AvramDividend.Classical.avram_reuse8_barrierValue_original_preruin_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:23:53.009166+00:00
-- url     : https://prove2.me/theorems/c4373bf2-d7cf-455d-a1f5-a5e9a3467462
-- title:
--   Original controlled pre-ruin barrier-value candidate is nonnegative by the disconnected scale-function branch
-- statement:
--   For the actual spectrally negative Lévy process, actual original dividend strategy and the original ruin time, the constant-barrier scale-function value is nonnegative at each strictly pre-ruin controlled reserve. The result is the precise pre-ruin value-function nonnegativity assumption used by BV and UBV verification when w is instantiated as barrierValue.
-- source:
--   Exact bridge of Proved 861b7656-5bc3-4d92-81da-da184060de56 (constant-barrier candidate nonnegative at every nonnegative capital) and Proved 03a69d71-1387-4410-83a2-1fe59054ebe6 (actual riskProcess nonnegative at every time strictly before formal ruin). It creates a natural direct consumer for the previously graph-disconnected calibration theorem. It supplies a verification-function side condition, not the stochastic expectation inequality.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_reuse8_barrierValue_original_preruin_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ barrierValue W a (riskProcess X x D t ω) := by sorry
