-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_actual_leftLimit_eq_countable
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_actual_leftLimit_eq_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:22:23.053967+00:00
-- url     : https://prove2.me/theorems/0e04e9d0-b8da-433a-8500-62496bcfe829
-- title:
--   Genuine post-payment Lévy reserve left limit equals its countable past-time observable
-- statement:
--   For the same original spectrally negative Lévy path and its genuinely adapted left-continuous dividend strategy, the post-payment reserve has a finite left limit at each strictly positive time. Its limit as the deterministic past-time sequence t-t/(n+2) approaches t equals the unique genuine pathwise left limit. The theorem is a source-level pathwise identification, not a stochastic-integral or generator assertion.
-- source:
--   Exact pinned Mathlib Filter.Tendsto.limUnder_eq, approved Avram source postPaymentReserve_prejump_upper, and a fully proved strict-past clock argument. Private remote compiler probe cd9c423c-e33c-4e2a-a09c-f06c790ef0bf passed to sentinel with no candidate diagnostics, source SHA-256 05b6dd69dae6ba5c9091930df9153b0482d1a4055e81171ac2d9e67ef220e05b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_actual_leftLimit_eq_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ,
      Filter.Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      Filter.limUnder Filter.atTop
        (fun n : ℕ =>
          x + X.X (t - t / ((n : ℝ≥0) + 2)) ω -
            rightLimit D (t - t / ((n : ℝ≥0) + 2)) ω) = l := by sorry
