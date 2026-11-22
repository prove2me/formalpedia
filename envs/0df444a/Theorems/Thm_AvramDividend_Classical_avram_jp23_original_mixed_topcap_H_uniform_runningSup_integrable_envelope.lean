-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp23_original_mixed_topcap_H_uniform_runningSup_integrable_envelope
-- name    : AvramDividend.Classical.avram_jp23_original_mixed_topcap_H_uniform_runningSup_integrable_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:46:59.525187+00:00
-- url     : https://prove2.me/theorems/d90014c8-e41f-494c-86ea-0e29578b1798
-- title:
--   True original mixed topcap nonlinear negative mark H uniformly dominated by integrable exponential running supremum
-- statement:
--   On the EXACT original mixed unbounded-variation Gaussian and finite negative-jump spectrally negative Levy source with infinite cap C=top, original stopped prepayment left-limit Y(t,omega) and fullnegative H kernel including the first ruin mark, prove existence of theta,K≥0 and integrable P random dominator B(omega)=K exp(theta*(x+runningSup X n omega)) such that |H((t,omega),z)|≤B(omega) at every physical clock t≤n and every mark z, and also retain the actual global HJB growth bound w(y)≤K exp(theta*y) for positive y. Reuse independently Proved original mixed topcap HJB-growth/running-sup L1 dominator (new theorem 76c58cc1), independently Proved UBV prepayment Function.leftLim upper bound by original runningSup (new theorem 06193581), and independently Proved original physical H abs envelope 0f2256b5. Use exp(-qt)≤1 for q>0, and monotonicity of w growth. This is concrete original-process stochastic L1 majorant for root-connected topcap J branch, not an assumed compensation result. Remaining actual physical Campbell centring remains an Open stochastic obligation.
-- source:
--   Root-connected d3408f6b, proven 0f2256b5, sources 76c58cc1 and 06193581 pending remote verdict, original mixed nonzero Levy/Gaussian assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp23_original_mixed_topcap_H_uniform_runningSup_integrable_envelope
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
    (hTop : C = ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      (∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)) ∧
      Integrable (fun ω : Ω =>
        K * Real.exp (θ * (x + runningSup X (n : ℝ≥0) ω))) P ∧
      ∀ (p : ((ℝ≥0 × Ω) × ℝ)),
        p.1.1 ≤ (n : ℝ≥0) →
        ‖H p‖ ≤
          K * Real.exp (θ * (x + runningSup X (n : ℝ≥0) p.1.2)) := by sorry
