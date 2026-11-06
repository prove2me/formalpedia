-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
-- name    : AvramDividend.Classical.avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:57:36.673513+00:00
-- url     : https://prove2.me/theorems/ae0f4de2-2c7b-48ea-950f-6e61dbb4d071
-- title:
--   True original-process weighted finite-band compensated increments have conditional mean zero without assumed rectangle rate
-- statement:
--   For actual original negative-band marked increments, any past measurable L² weight times the centred count has zero conditional expectation given the original filtration, assuming the standard measurability and finite L² terms. The physical rectangle-rate premise is discharged from the original Lévy future rectangle source, not posited as an independent stochastic axiom.
-- source:
--   Combines accepted source ea8700f6, the new P4-S3 arbitrary-cell physical predictable rectangle wrapper, and Proved P4-G conditional-zero theorem c5e75f35.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
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
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    P[(fun ω => H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s] =ᵐ[P] 0 := by sorry
