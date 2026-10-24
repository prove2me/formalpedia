-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
-- name    : AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T00:34:33.155062+00:00
-- url     : https://prove2.me/theorems/02561675-7798-4512-a22d-28112e3f86d9
-- title:
--   Pathwise Stieltjes reward translation at the first barrier upcrossing
-- statement:
--   For a finite first strict upcrossing u of the barrier gap a−x by a spectrally negative Lévy path, the Stieltjes dividend measure of the original barrier strategy on the translated interval (u,u+t] equals the Stieltjes measure of the running supremum of the shifted increments on (0,t]. This is a pathwise identity, conditional only on compact boundedness for the relevant interval; it isolates the time-translation step from the separate random-time independence and ruin-cutoff limit needed for the value factorization.
-- source:
--   Pathwise consequence of Proved firstUpcrossing_attains_peak (UUID 473109a5-7650-47ba-b397-29e7480e709e), Proved barrierStrategy_after_firstUpcrossing_shift (UUID 45c142a6-d973-4377-b915-fde631802cfd), and the pinned StieltjesFunction.measure_Ioc interval formula. It corrects the shifted-path argument needed by Open barrierStrategy_value_eq_killed_exit_mul_supValue (UUID 8fc83520-78bb-4a8c-a394-12b04a096b66); it does not invoke the similarly named Open theorem whose right side uses the unshifted runningSup X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0,
      BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)) →
      (dividendMeasure (barrierStrategy X x a) ω)
          (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
        (dividendMeasure
          (fun r _ =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by sorry
