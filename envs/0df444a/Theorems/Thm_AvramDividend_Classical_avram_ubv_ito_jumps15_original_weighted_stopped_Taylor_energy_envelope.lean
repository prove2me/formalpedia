-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps15_original_weighted_stopped_Taylor_energy_envelope
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps15_original_weighted_stopped_Taylor_energy_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:24:15.44422+00:00
-- url     : https://prove2.me/theorems/1b5f41b1-f5f1-4a77-87d4-232ccde95e39
-- title:
--   Original ruin-stopped Lévy Taylor jump envelope survives a bounded physical weight and arbitrary further stop
-- statement:
--   For Avram's actual spectrally negative Lévy process and dividend control, the globally proved negative-mark Taylor remainder energy envelope remains valid after multiplying by any physical time-space weight of absolute value at most one and stopping at any additional original physical clock. This source-exact weighted interface gives the same uniform M*min(1,z²) Lévy-integrable domination for the discounted and localised jump integrands entering the stopped Itô–Meyer formula. It imports the genuine previously Proved original stopped envelope 5eef1de0; no Brownian or equality-in-law process is substituted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps15_original_weighted_stopped_Taylor_energy_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (a : (ℝ≥0 × Ω) → ℝ) (ha : ∀ p, |a p| ≤ 1)
    (σ : Ω → ℝ≥0) :
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1.1 ≤ σ p.1.2 then a p.1 * HS p else 0
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ p : ((ℝ≥0 × Ω) × ℝ), p.2 < 0 →
        |G p| ≤ M * min 1 (p.2 ^ 2) := by sorry
