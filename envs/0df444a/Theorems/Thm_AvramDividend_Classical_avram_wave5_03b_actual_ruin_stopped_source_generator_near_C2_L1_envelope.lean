-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:26:14.698404+00:00
-- url     : https://prove2.me/theorems/9b510aa0-fdb5-447f-a79d-823d7328cbcc
-- title:
--   Actual stopped controlled source generator Taylor correction has a uniform C2 quadratic near-mark bound
-- statement:
--   For the original spectrally negative Lévy source, same adapted dividends and prepayment left-limit reserve, C2 regularity on (0,C) yields a single uniform quadratic absolute-value bound M z² for the ruin-stopped, full source Taylor-corrected nonlinear jump kernel at every strictly interior compact reserve value and all sufficiently small negative marks. The bound is on the actual controlled kernel and is the near-zero L1 generator-drift integrability ingredient, distinct from its already proved L2 energy. It does not assert the missing source predictable compensator.
-- source:
--   Canonical source generator near-C2 bound 485f09e2-781b-4471-a0f7-93c1a4abffb4, actual source controlled prepayment Taylor-generator pointwise identity e336f7e2-a55f-48e8-b33e-54114f97e681. Survival is actual ruinTime indicator, not a free PRM. No first absolute jump moment used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u + δ) (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∃ r M : ℝ, 0 < r ∧ r ≤ min (u + δ) 1 ∧ 0 ≤ M ∧
      ∀ p : ℝ≥0 × Ω, Y p ∈ Icc (u + δ) v →
        ∀ z ∈ Ioo (-r) 0, |HS (p,z)| ≤ M * z ^ 2 := by sorry
