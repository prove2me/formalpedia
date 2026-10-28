-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
-- name    : AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:55:58.368903+00:00
-- url     : https://prove2.me/theorems/443876a6-e856-480c-8a37-40deba77bd09
-- title:
--   Post-upcrossing barrier-dividend Stieltjes measure translation without boundedness premise
-- statement:
--   After the first finite upcrossing, the original barrier dividend Stieltjes mass over (u,u+t] equals the running maximum dividend Stieltjes mass of the shifted future Lévy increments over (0,t]. Every Lévy sample path is already bounded on finite intervals, so the compact-boundedness side-condition in the established pathwise theorem is discharged automatically.
-- source:
--   Direct root-connected pathwise ingredient for strong-Markov barrier value child 79978d61-9d1f-4b20-b8a5-114797a8e380. Imports Proved pathwise measure translation 02561675-7798-4512-a22d-28112e3f86d9 and compact path boundedness c2066587-8d80-45bd-a4dc-0d24c616ddf8, with no W/scale-function premises.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0,
      (dividendMeasure (barrierStrategy X x a) ω)
          (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
        (dividendMeasure
          (fun r _ =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  sorry
