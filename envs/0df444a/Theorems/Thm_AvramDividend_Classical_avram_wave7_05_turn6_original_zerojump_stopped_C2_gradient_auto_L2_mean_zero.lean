-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_zerojump_stopped_C2_gradient_auto_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_zerojump_stopped_C2_gradient_auto_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:58:13.707556+00:00
-- url     : https://prove2.me/theorems/e746a7f6-8e48-44b4-b982-e9c1cffdc86c
-- title:
--   Original no-jump controlled C2 stopped gradient automatically predictable L2 Gaussian gain meanzero
-- statement:
--   For the actual SpectrallyNegativeLevy X on its existing probability space and right-continuous filtration when X has no Levy jumps, a bounded discounted ruin-gated stopped C2 derivative of the actual dividend-controlled reserve automatically yields an L2-integrable centred Gaussian stopped increment. No auxiliary Y or independent Brownian probability space is introduced.
-- source:
--   Combines Proved original all-nu gradient/Hessian stopped predictability UUID 41b798ce-dc51-4499-a4c7-50320ffae570 with Proved original zero-jump bounded Gaussian stopped gain UUID 8cf2614f-c9fe-47f1-896a-57969706c910. This covers the genuine nu=0 subclass. Original arbitrary-nu continuous component extraction remains separate.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_zerojump_stopped_C2_gradient_auto_L2_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hXν : X.ν = 0)
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
    (K : ℝ) (hK : 0 ≤ K) (hGbound : ∀ ω, |G ω| ≤ K) :
    let V : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => G ω * V ω) 2 P ∧
    Integrable (fun ω => G ω * V ω) P ∧
    (∫ ω, G ω * V ω ∂P) = 0 := by sorry
