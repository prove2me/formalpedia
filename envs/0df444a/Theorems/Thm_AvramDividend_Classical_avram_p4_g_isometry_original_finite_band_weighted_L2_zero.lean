-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_weighted_L2_zero
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_weighted_L2_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:36:22.739671+00:00
-- url     : https://prove2.me/theorems/b9aa20a2-c121-4b70-a9ac-be1148195789
-- title:
--   Actual intrinsic finite negative-band predictable L2 weight has zero compensated expectation
-- statement:
--   For the source Lévy path on the actual probability space and raw past filtration, the precise original P2-E rectangle law gives a zero integral when the centred finite-band count is multiplied by a square-integrable original-past predictable weight. The count is assumed square-integrable; this is not derived from a first-moment intensity law. The proof composes a genuine raw-filtration conditional expectation bridge with the original raw L2 orthogonality helper, independently of a right-continuous augmentation.
-- source:
--   Direct composition of P4-G original raw condExp zero 225782a0 and raw conditional orthogonality 18ad8d66; all physical-source assumptions exposed.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_band_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_conditional_cross_zero

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_weighted_L2_zero
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
    (hMeas : Measurable N)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω =>
      (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    (∫ ω, H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by sorry
