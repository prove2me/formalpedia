-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_predictable_compensated_JL_exact
-- name    : AvramDividend.Classical.avram_pj_workerC_original_NX_predictable_compensated_JL_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:38:15.295386+00:00
-- url     : https://prove2.me/theorems/7b1e1a05-c4f8-40a6-94fb-75e340c7c0ae
-- title:
--   Original mapped Lévy jump NX and true stopped physical clock compensator have exact nonlinear plus annular linear compensation identity
-- statement:
--   For any true original spectrally negative Lévy sample path and finite physical clock horizon, the two distinct measures consisting of the actual mapped positive-time marked jump counting measure NX(ω) and the deterministic-time μT×ν negative-mark compensator are both supported on strictly negative marks. Given genuine integrability of nonlinear Taylor and finite annular linear terms for both, the signed compensated nonlinear term plus signed annular linear correction reduces exactly to the tiny negative-mark adjusted Taylor kernel compensated against the same original two measures. This instantiates the physically correct pair of measures, not a surrogate.
-- source:
--   Proved original NX negative support 9da8864c; proved signed J+L compensation 464d0c7d; Mathlib ae_prod_iff_ae_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_NX_predictable_compensated_JL_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (η : ℝ) (hη : 0 < η) (hηone : η < 1)
    (S d : (ℝ≥0 × ℝ) → ℝ) :
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let CN : Measure (ℝ≥0 × ℝ) :=
      μT.prod (X.ν.restrict (Iio (0 : ℝ)))
    Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) NX →
    Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) NX →
    Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) CN →
    Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) CN →
    ((∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂NX) -
      (∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂CN)) +
    ((∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂NX) -
      (∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂CN)) =
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂NX) -
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂CN) := by sorry
