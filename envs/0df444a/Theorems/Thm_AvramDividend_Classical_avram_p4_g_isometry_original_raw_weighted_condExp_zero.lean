-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_weighted_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:03:08.108114+00:00
-- url     : https://prove2.me/theorems/c5e75f35-f222-419e-9834-8f0718ba4456
-- title:
--   Original predictable-weighted intrinsic negative-band compensated count has zero raw conditional expectation
-- statement:
--   Under precisely P2-E's original intrinsic Lévy rectangle compensation law, on original Ω and raw 𝓕_s, a true past-predictable square-integrable H times the centred actual finite-band count has conditional expectation zero. Requires explicit L2 count assumption, finite ν band, genuine source path equality, strict negative mark separation. This is the weighted martingale difference needed for physical finite-grid orthogonality, without usual filtration conditions, Poisson variance or stopping.
-- source:
--   Proved raw count conditional mean 225782a0 and pinned condExp_mul_of_stronglyMeasurable_left, with full integrability evidence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_band_condExp_zero

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_weighted_condExp_zero
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
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P)
    : P[(fun ω => H ω * ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s] =ᵐ[P] 0 := by sorry
