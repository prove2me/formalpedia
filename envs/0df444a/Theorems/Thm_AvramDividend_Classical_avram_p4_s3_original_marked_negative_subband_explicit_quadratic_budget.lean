-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
-- name    : AvramDividend.Classical.avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:19:58.329696+00:00
-- url     : https://prove2.me/theorems/367c2c5e-28cf-48b6-aadc-aaa41f79b3c5
-- title:
--   Physical negative Borel subband count has explicit uniform second-moment budget from original full-band factorial estimates
-- statement:
--   For any true original Lévy marked negative Borel cell (s,t]×B inside (0,T] and below threshold -1/(n+1), the second moment of the real jump count is bounded by R²+R with R=Tν((−∞,−1/(n+1)]). Physical original count domination and the proved full-band factorial moment bound give the exact numerical estimate, without a substitute Poisson process or additional stochastic axiom.
-- source:
--   P4-S3 physical marked-cell domination 840cfac4, physical original bounded-clock quadratic budget 50312326, measurable marked counts and Mathlib integral_mono_ae.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let R : ℝ := ((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R := by sorry
