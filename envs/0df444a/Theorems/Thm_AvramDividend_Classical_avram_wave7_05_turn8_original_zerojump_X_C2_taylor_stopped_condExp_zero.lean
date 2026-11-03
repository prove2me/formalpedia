-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_zerojump_X_C2_taylor_stopped_condExp_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn8_original_zerojump_X_C2_taylor_stopped_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:53:01.490737+00:00
-- url     : https://prove2.me/theorems/4bdc5178-5aa8-48cf-9044-64a0430ba477
-- title:
--   Canonical pure-Gaussian original X stopped C2 Taylor residual has conditional mean zero
-- statement:
--   For the exact canonical original process X with zero Lévy jump measure, original filtration, dividend-controlled left-limit reserve and ruin gate, the stopped C2 Taylor residual G Δ(X-tc) + H/2((Δ(X-tc))²-hσ²) is integrable and has conditional expectation zero at the stopping-time sigma algebra under explicit L1 product integrability. No second process is used.
-- source:
--   Pure Gaussian specialisation Y=X Jsmall=Jlarge=0 of original all-nu stopped C2 Gaussian conditional Taylor identity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_taylor_stopped_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn8_original_zerojump_X_C2_taylor_stopped_condExp_zero
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
    (hGI : Integrable (fun ω => G ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHI : Integrable H P)
    (hH2I : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
    let R : Ω → ℝ := fun ω =>
      G ω * V ω + (1 / 2 : ℝ) * H ω *
        (V ω ^ 2 - (h : ℝ) * X.σ ^ 2)
    Integrable R P ∧
      P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
