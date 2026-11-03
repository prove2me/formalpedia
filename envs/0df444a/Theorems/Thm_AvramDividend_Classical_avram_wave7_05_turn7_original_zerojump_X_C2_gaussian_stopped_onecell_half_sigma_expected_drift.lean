-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_stopped_onecell_half_sigma_expected_drift
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_stopped_onecell_half_sigma_expected_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:24:13.048835+00:00
-- url     : https://prove2.me/theorems/1962ca63-67a1-4238-a7cb-d1035d111b28
-- title:
--   Direct original zero-jump source stopped C2 Gaussian Ito expected drift with exact sigma squared over two
-- statement:
--   For the given spectrally negative Levy X itself, if X has zero jump measure, the stopped C2 controlled reserve Gaussian cell is integrable and its expected gradient plus half-Hessian second-order increment equals sigma squared over two times the cell duration and the expected actual source Hessian. It uses the original Omega/P/filtration, dividend right limit and original ruin stopping, with no auxiliary Gaussian witness.
-- source:
--   Directly specialise the remotely Proved all-nu original-source C2 Gaussian one-cell expected-drift theorem with Y=X and identically zero jump fields, using the algebraic source decomposition. No independent sample space.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_source_C2_gaussian_onecell_ito_half_sigma_expected_drift

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_stopped_onecell_half_sigma_expected_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG) (hHbound : ∀ ω, |H ω| ≤ BH) :
    let V : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => G ω * V ω + (1 / 2 : ℝ) * H ω * V ω ^ 2) P ∧
      (∫ ω, G ω * V ω + (1 / 2 : ℝ) * H ω * V ω ^ 2 ∂P) =
        (((h : ℝ) * X.σ ^ 2) / 2) * (∫ ω, H ω ∂P) := by sorry
