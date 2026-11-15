-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a125_original_negative_Borel_void_deficit_between_first_factorial_moments_20261114
-- name    : AvramDividend.Classical.avram_a125_original_negative_Borel_void_deficit_between_first_factorial_moments_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:33:20.392943+00:00
-- url     : https://prove2.me/theorems/cb7653e3-ff12-4c31-a9b8-91a0ce111e71
-- title:
--   Original finite-negative-activity Borel marked-jump nonvoid probability lies between first moment minus factorial second moment and first moment
-- statement:
--   For the true physical Borel negative jump count on the original Lévy process, the probability of at least one marked jump over a finite interval differs from its first moment tν(B) by at most its second factorial moment (tν(B))². Equivalently tν(B)−(tν(B))² ≤ 1−P(no jump) ≤ tν(B). This uses exact original first and second factorial count moments and the pointwise integer-count inequalities k − k(k−1) ≤ 1_{k>0} ≤ k. No Poisson count distribution or Gaussian decomposition is assumed.
-- source:
--   Proved JA35 original negative Borel real count first moment, Proved A20 exact raw second moment and Proved physical Borel natural count realisation. Integrate integer inequalities against original P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a125_original_negative_Borel_void_deficit_between_first_factorial_moments_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let rate : ℝ := (t : ℝ) * (X.ν B).toReal
    let void : ℝ :=
      (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B) = 0}).toReal
    rate - rate ^ 2 ≤ 1 - void ∧ 1 - void ≤ rate := by sorry
