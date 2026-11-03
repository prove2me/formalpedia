-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:55:40.13621+00:00
-- url     : https://prove2.me/theorems/0c22bf97-f037-4d32-ba42-f1ff1f2062b4
-- title:
--   Canonical X minus source jumps stopped C2 Gaussian gradient has exact L2 isometry and zero mean
-- statement:
--   On the canonical spectrally negative Lévy probability space, define M_t = X.X_t - t X.c - Jsmall_t - Jlarge_t. Under an explicit same-space Gaussian Lévy-Itô representation Y with equal sigma and zero Lévy jump measure, the bounded stopped original-controlled C2 gradient times the M increment is square-integrable, integrable, centred and has exact second moment h X.sigma squared times E[G squared]. The reserve x+X.X-rightLimit D and original ruin time remain in G. The extraction representation is a hypothesis requiring separate proof.
-- source:
--   Remote-Proved Wave6 original stopped predictable weighted Gaussian variance UUID 3b8f471a-fcbd-4835-b339-46d13701ea9d and Wave7 original stopped Gaussian bounded gain L2 mean zero UUID 8cf2614f-c9fe-47f1-896a-57969706c910; accepted source derivative measurability UUID 41b798ce-dc51-4499-a4c7-50320ffae570. Pathwise source decomposition replaces centred Y increments with X-minus-jump residual increments.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (BG : ℝ) (hBG : 0 ≤ BG)
    (hGbound : ∀ ω, |G ω| ≤ BG) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : Ω → ℝ := fun ω =>
      M (τ ω + h) ω - M (τ ω) ω
    MemLp (fun ω => G ω * V ω) 2 P ∧
      Integrable (fun ω => G ω * V ω) P ∧
      (∫ ω, G ω * V ω ∂P) = 0 ∧
      (∫ ω, (G ω * V ω) ^ 2 ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * G ω ∂P) := by sorry
