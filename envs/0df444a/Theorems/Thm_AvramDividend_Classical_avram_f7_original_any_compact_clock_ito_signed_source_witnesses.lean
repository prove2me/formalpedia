-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f7_original_any_compact_clock_ito_signed_source_witnesses
-- name    : AvramDividend.Classical.avram_f7_original_any_compact_clock_ito_signed_source_witnesses
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:43:21.715195+00:00
-- url     : https://prove2.me/theorems/f53cf458-eded-4a53-9eea-312405379326
-- title:
--   Original capped unbounded-variation Ito-Meyer centred martingale and signed-residual witnesses for every compact clock
-- statement:
--   For each genuinely stopped and integrable original payoff F_k in the unbounded-variation Levy dividend process, construct actual same-source compensated martingale, nonpositive HJB drift and dividend-accounting residual M,G,H; M,G,H integrable, E[M]=0, G+H≤0 almost surely and F_k≤w(x)+M+G+H almost surely. No artificial Markov or Poisson independence assumption is inserted. Existing accepted Ito-budget integration makes the expected inequality an algebraic consequence; this child isolates original physical stochastic calculus.
-- source:
--   Direct source-faithful decomposition of e26b843b's expected-payoff clause. Classical Ito-Meyer plus HJB generator sign and Stieltjes right-payment accounting provide the named integrable signed source witnesses; the later conditional bridge integrates their inequality.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_f7_original_any_compact_clock_ito_signed_source_witnesses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hStop : (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))))
    (hBound : (∀ k ω, σ k ω ≤ τ ω))
    (hExact : (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨
                (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal))
    (hMeas : (∀ k, Measurable (F k)))
    (hInt : (∀ k, Integrable (F k) P))
    (hNonneg : (∀ k, 0 ≤ᵐ[P] F k)) :
    ∀ k : ℕ, ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + M ω + G ω + H ω) := by sorry
