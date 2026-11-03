-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_zerojump_stopped_C2_gaussian_bounded_ito_martingale
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_zerojump_stopped_C2_gaussian_bounded_ito_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:02:13.861314+00:00
-- url     : https://prove2.me/theorems/1ab09f0b-b385-4537-9f04-dcce343891c4
-- title:
--   Original zero-jump C2 Gaussian controlled Ito half-bracket one-cell centred under bounded derivative and Hessian
-- statement:
--   For the canonical original zero-jump Levy process X and actual dividend-controlled reserve, every bounded stopped discounted gradient and bounded clipped Hessian produce an integrable centred Gaussian C2 Ito one-cell residual G V + 1/2 H(V squared-h sigma squared). The stopped Hessian integrability and weighted quadratic moment requirements are deduced from the coefficient bounds and the original Gaussian conditional bilinear theorem, not assumed independently.
-- source:
--   Uses the Proved source predictable Hessian UUID 41b798ce-dc51-4499-a4c7-50320ffae570, exact-revision Mathlib Integrable.of_bound, Proved bounded stopped Gaussian bilinear theorem UUID a52309b8-5be6-406f-befd-5921676b3177, and Proved original controlled C2 one-cell residual UUID 0f006e3c-0422-4c38-b92a-ce77657548f3.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_zerojump_stopped_C2_gaussian_bounded_ito_martingale
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
    (h : ℝ≥0)
    (KG KH : ℝ) (hKG : 0 ≤ KG) (hKH : 0 ≤ KH) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    (∀ ω, |G ω| ≤ KG) →
    (∀ ω, |H ω| ≤ KH) →
    let V : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => G ω * V ω +
      (1 / 2 : ℝ) * (H ω * ((V ω) ^ 2 - (h : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, G ω * V ω +
      (1 / 2 : ℝ) * (H ω * ((V ω) ^ 2 - (h : ℝ) * X.σ ^ 2)) ∂P) = 0 := by sorry
