-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:26:56.936395+00:00
-- url     : https://prove2.me/theorems/64618901-0227-4435-a75b-69df98b58b92
-- title:
--   Actual BV future full-mark jump expectation satisfies exact positive Lévy-rate interval balance
-- statement:
--   For the true original BV finite-activity spectrally negative Lévy X, any 0<s≤t, the expected literal count of all nonzero jumps on (s,t] obeys s·X.ν(Iio0)+E[N_X((s,t]×ℝ)]=t·X.ν(Iio0). This gives the exact positive full-mark stationary intensity on future source intervals as a finite ENNReal balance, using already proved original source time additivity and original full-mark first moment at initial horizons. No external clock grids, Poisson copy, arbitrary mark-rate compensator, or past-event independence is assumed.
-- source:
--   Proof from canonically Proved source time additivity 0b578fb5 and original total first moment grid-free 4d7761f5 on the same source process; take A=Ω and B=ℝ, then rewrite the 0-to-s and 0-to-t total rates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_time_additive
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_fullmark_future_interval_intensity_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    (s : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) +
      (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P) =
    (t : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
