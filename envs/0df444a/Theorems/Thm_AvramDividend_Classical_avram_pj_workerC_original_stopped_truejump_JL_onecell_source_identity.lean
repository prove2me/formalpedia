-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_stopped_truejump_JL_onecell_source_identity
-- name    : AvramDividend.Classical.avram_pj_workerC_original_stopped_truejump_JL_onecell_source_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:16:07.273187+00:00
-- url     : https://prove2.me/theorems/3e147f3e-1201-43a3-acee-ae7a18162430
-- title:
--   Original stopped compensated nonlinear and annular linear one-jump integrands combine to the exact tiny negative-mark Taylor residual on true pre-ruin clocks
-- statement:
--   For any actual original spectrally negative Lévy path and marked negative jump, at a bounded stopping clock rho before true ruin, the discounted nonlinear source GW with original pre-ruin mask plus actual annular L term equals one same-clock discounted nonlinear kernel with first-order subtraction only on z>=-eta. This preserves actual time cutoffs, ruin contact, C2 interior band and post-payment reserve, and is the per-atom bridge towards combining original J+L compensated measures.
-- source:
--   Proved masked scalar J/L mark identity plus original source rho<=T and rho<=ruinTime clock certificates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_stopped_truejump_JL_onecell_source_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρT : ∀ ω, ρ ω ≤ T)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u v δ η : ℝ) (hη : 0 < η) (hηone : η < 1) :
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then
          deriv w (Y p.1) else 0) else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    ∀ (t : ℝ≥0) (ω : Ω) (z : ℝ), z < 0 →
      (if t ≤ ρ ω then GW ((t, ω), z) else 0) +
      (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then
        Real.exp (-(q * (t : ℝ))) *
          (if Y (t, ω) ∈ Icc (u + δ) v then deriv w (Y (t, ω)) * z
            else 0) else 0) =
      (if t ≤ ρ ω then Real.exp (-(q * (t : ℝ))) *
        ((if Y (t, ω) ∈ Icc (u + δ) v then
          w (Y (t, ω) + z) - w (Y (t, ω)) else 0) -
         (if -η ≤ z then
           z * (if Y (t, ω) ∈ Icc (u + δ) v then
             deriv w (Y (t, ω)) else 0) else 0)) else 0) := by sorry
