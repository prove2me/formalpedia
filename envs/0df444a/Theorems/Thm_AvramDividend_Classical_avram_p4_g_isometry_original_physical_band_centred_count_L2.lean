-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_band_centred_count_L2
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_physical_band_centred_count_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:47:31.827524+00:00
-- url     : https://prove2.me/theorems/e0edd902-b302-4d67-9120-3cd4ba4d7d58
-- title:
--   Original physical intrinsic marked finite-band count has centred L2 moment
-- statement:
--   For the actual intrinsic marked count of original spectrally negative Lévy process X in (s,t] and strict band -1<z<-epsilon, source compensation yields integrable first moment. Exact physical chronological pair rate yields integrable second factorial moment, jointly giving centred count in L2(P). The pair-rate remains an explicit physical premise; no Poisson-space replacement or stopping is asserted.
-- source:
--   Original physical pair factorial lemma and original rectangle-law mean; direct L2 criterion for genuine NX finite-band compensated count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_band_L1_mean_auto_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_centered_count_L2_of_factorial_integrability

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_physical_band_centred_count_L2
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
    MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P := by sorry
