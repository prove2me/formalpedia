-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_weighted_condExp_zero_meas_and_rate_auto
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_weighted_condExp_zero_meas_and_rate_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:58:55.505389+00:00
-- url     : https://prove2.me/theorems/23c5d5d5-479a-4476-80a0-17c8fc452523
-- title:
--   Fully physical negative-band predictable weighted increment has conditional mean zero with automatic measurability, finite mass and rectangle compensation
-- statement:
--   The exact marked negative-band count of an original spectrally negative Lévy process, weighted by any past L² random variable, has conditional expectation zero after compensating by (t-s)ν(B), provided the compensated count belongs to L². Measurability, finite Lévy mass and the future rectangle rate are proved from the original process rather than assumed.
-- source:
--   Uses Proved original mark count measurability 21acd1ce, separated Lévy mark finiteness 86086cb2, and the new P4-S3 weighted conditional-zero no-rate helper, all for the true original process.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_weighted_condExp_zero_meas_and_rate_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    P[(fun ω => H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s] =ᵐ[P] 0 := by sorry
