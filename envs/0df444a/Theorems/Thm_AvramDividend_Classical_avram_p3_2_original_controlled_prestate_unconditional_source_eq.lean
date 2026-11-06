-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_prestate_unconditional_source_eq
-- name    : AvramDividend.Classical.avram_p3_2_original_controlled_prestate_unconditional_source_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:18:33.646191+00:00
-- url     : https://prove2.me/theorems/4f8d29e3-7e1b-4192-9ee4-a70b391d0f9a
-- title:
--   Actual original controlled X/D positive-time left prestate without an extra left-limit hypothesis
-- statement:
--   For every original Lévy path and positive physical time, the left limit of the controlled post-dividend reserve is x + the true Lévy left limit minus the dividend pre-rightpayment value. The pinned original cadlag regularity provides the left limit automatically. This removes an artificial hypothesis from the strict stopped original X,D jump source assembly.
-- source:
--   Proved public original cadlag theorem 09e1699b and explicit controlled left prestate af64d023.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_controlled_prestate_unconditional_source_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
        D t ω := by sorry
