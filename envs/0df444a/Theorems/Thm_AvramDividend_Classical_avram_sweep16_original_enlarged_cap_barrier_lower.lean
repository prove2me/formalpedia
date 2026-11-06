-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower
-- name    : AvramDividend.Classical.avram_sweep16_original_enlarged_cap_barrier_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:47:06.440053+00:00
-- url     : https://prove2.me/theorems/0e338c90-f202-4110-b622-88c409a25e95
-- title:
--   Original c-star barrier payoff lower bound for all enlarged dividend caps
-- statement:
--   For an actual standing spectrally negative Lévy surplus process, the proved c-star barrier-attainment theorem supplies a capped admissible policy achieving vcstar at the c-star cap. The exact original value-function monotonicity under cap enlargement transports that lower bound to every C with cstar W ≤ C. This is a genuine unconditional lower bound for the original process; no stopped Ito or upper-verification assertion is assumed.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_monotone_cap
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment


open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_enlarged_cap_barrier_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (C : ℝ≥0∞) (hCap : cstar W ≤ C) :
    ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal (vcstar W x) ≤ valueFunctionLe X q C x := by sorry
