-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_stopped_prepayment_JL_compensation
-- name    : AvramDividend.Classical.avram_pj_workerC_original_NX_stopped_prepayment_JL_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:42:59.758245+00:00
-- url     : https://prove2.me/theorems/59d9fd34-8267-4307-9317-d57a5ddbb9e3
-- title:
--   Genuine original stopped true-prepayment nonlinear Taylor J plus annular L compensate exactly under actual counted jumps and Lévy physical-time measure
-- statement:
--   For a true original spectrally negative Lévy reserve and a stopped clock rho, define the nonlinear S with the original left-limit controlled reserve Y, spatial C2 band and discount, and the linear derivative d, both masked at the same original clock. Against the original mapped positive-time jumps NX and actual finite physical-time × true negative Lévy ν compensator CN, four natural integrability hypotheses imply the compensated J+L source equals exactly the nonlinear residual with only the marks z≥-eta linear subtraction. It retains the actual physical prepayment process and clock, rather than only generic negative mark algebra.
-- source:
--   Public Proved original path NX strict negative support and 464d0c7d exact two-measure compensated mark kernel; true source Y from original reward80.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_NX_stopped_prepayment_JL_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0)
    (u v δ η : ℝ) (hη : 0 < η) (hηone : η < 1) :
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
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let S : (ℝ≥0 × ℝ) → ℝ := fun p =>
      if p.1 ≤ ρ ω then
        Real.exp (-(q * (p.1 : ℝ))) *
        (if Y (p.1, ω) ∈ Icc (u + δ) v then
          w (Y (p.1, ω) + p.2) - w (Y (p.1, ω)) else 0)
      else 0
    let d : (ℝ≥0 × ℝ) → ℝ := fun p =>
      if p.1 ≤ ρ ω then
        Real.exp (-(q * (p.1 : ℝ))) *
        (if Y (p.1, ω) ∈ Icc (u + δ) v then
          deriv w (Y (p.1, ω)) else 0)
      else 0
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
