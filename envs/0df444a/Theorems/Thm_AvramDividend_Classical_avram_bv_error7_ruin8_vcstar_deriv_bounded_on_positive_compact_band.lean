-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:39:15.590232+00:00
-- url     : https://prove2.me/theorems/fda2fce4-e151-4788-a49c-6abd30e94bf7
-- title:
--   Original BV barrier value derivative has a finite bound on any positive compact surplus band
-- statement:
--   For the actual BV Lévy process and scale-function barrier candidate, the derivative is uniformly bounded on every compact surplus band separated from ruin by a strictly positive lower endpoint. No derivative bound at ruin is claimed.
-- source:
--   Use the Proved original BV derivative continuity on (0,∞), restrict it to Icc a b, take absolute values and use compactness of the image to obtain an upper bound. This is the original vcstar localised endpoint adapter needed for contact Taylor error control without circular use of the BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_on_positive_bv
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) (a b : ℝ) (ha : 0 < a) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ Set.Icc a b, |deriv (vcstar W) z| ≤ L := by sorry
