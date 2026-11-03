-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:20:38.485958+00:00
-- url     : https://prove2.me/theorems/f2efea1f-14aa-4f18-b023-ea79a35d14ec
-- title:
--   Original controlled BV ruin-stopped strict interior is jointly measurable on physical time and sample space
-- statement:
--   The strict pre-ruin, strictly positive and sub-cap predictable left-limit region for the actual controlled Lévy source is measurable in Borel physical time times its original sample space, without auxiliary sample spaces, integrability hypotheses or a substitute stopping time. The proof uses the established original left-limit strong predictability, its strong progressiveness on bounded time intervals and source ruin-time measurability.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), original controlled Lévy process, measurable pre-ruin interior used in W7-17 accepted stopped expectation lemmas b4a4ea2a, eb3cbab8 and eafa21bb; removes their explicit MeasurableSet S assumption by local predictability and the original ruin clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (C : ℝ≥0∞) :
    MeasurableSet
      {p : ℝ≥0 × Ω |
        p.1 ≤ T ∧
        (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C} := by sorry
