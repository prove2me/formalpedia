-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp20261122_zero_clock_original_fullreward_le_initial
-- name    : AvramDividend.Classical.avram_jp20261122_zero_clock_original_fullreward_le_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:48:12.91566+00:00
-- url     : https://prove2.me/theorems/fdb588d3-c454-4aee-9266-e5872dae6ec1
-- title:
--   Original mixed finite-activity zero-clock full stopped reward bounded by initial verification w
-- statement:
--   With the exact original mixed negative Levy finite-activity source, stochastic dividend strategy, clipped stopping clock sigma and full right-dividend cash (inclusive clock Iic), prove for each sample omega with sigma omega=0 that the full original reward F omega is bounded by the initial verification w x. This is the true clock-zero payoff and right-paid initial dividend bound, independent of any positive-time Ito-Meyer approximation. The proof specialises existing Proved exact-clock-zero source rather than assuming F has no initial dividend.
-- source:
--   Avram original ruin-clipped cash. Uses Proved avram_p4_f8_original_exact_clock_zero_reward_le_initial (23c3965a-004e-4e88-b9c3-3df0abaf41cb), linked to root through f2f69b1a-ad52-4f7a-878f-1d03f219b788 when used by its zero/positive split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp20261122_zero_clock_original_fullreward_le_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hFiniteCap : C ≠ ⊤) :
    ∀ ω : Ω, σ ω = 0 → F ω ≤ w x := by sorry
