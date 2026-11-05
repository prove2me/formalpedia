-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:58:48.900132+00:00
-- url     : https://prove2.me/theorems/e3be3ca7-3ce1-4f0e-a479-f0ff856190b8
-- title:
--   Original physical separated-band factorial moment from chronological pair intensity
-- statement:
--   For the actual intrinsic X jump count on a finite separated negative Borel band, if K is the actual chronological ordered-pair count satisfying the pathwise J(J−1)=2K identification and its exact original probability-space lintegral is half the squared physical Lévy rate, then the factorial count is integrable and its real expectation is the squared rate. The original chronological pair rate remains an explicit source premise.
-- source:
--   Source-exact original NX marked count, chronological pair identity, pinned MeasureTheory.integrable_toReal_of_lintegral_ne_top and integral_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (K : Ω → ℝ≥0∞) (hKMeas : Measurable K)
    (hPhysicalPair : ∀ ω,
      (N ω).toReal * ((N ω).toReal - 1) = 2 * (K ω).toReal)
    (hPairMean :
      (∫⁻ ω, K ω ∂P) = ENNReal.ofReal
        (((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2 / 2)) :
    Integrable (fun ω =>
      (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2 := by sorry
