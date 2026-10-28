-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero
-- name    : AvramDividend.Classical.barrierStrategy_plus_linear_drain_ruinTime_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:31:13.364161+00:00
-- url     : https://prove2.me/theorems/1bf6de32-30fd-445e-919e-78b7e0c63915
-- title:
--   Zero-barrier control with a linear drain ruins instantly along every path
-- statement:
--   For every spectrally negative Lévy process and nonnegative initial reserve, the zero-barrier cumulative dividends plus an additional payment t force the controlled reserve negative at every strictly positive time. The ruin time is therefore exactly zero, pathwise with no assumptions on Brownian regularity. This is the explicit immediate-ruin strategy needed to audit the missing boundary condition in the verification theorem.
-- source:
--   The proved linear-drain reserve negativity and the proved order-theoretic first-ruin-time zero lemma.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_zero_of_negative_every_positive_time
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_plus_linear_drain_ruinTime_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (ω : Ω) :
    ruinTime X x
      (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω = 0 := by sorry
