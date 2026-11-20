-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_bounded_ruinclock_finite_mesh_threechannel_limits
-- name    : AvramDividend.Classical.avram_jump6_B_original_bounded_ruinclock_finite_mesh_threechannel_limits
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T12:32:03.853666+00:00
-- url     : https://prove2.me/theorems/f85f4eb6-b0ab-42f5-9196-c2331aec3d7e
-- title:
--   Original bounded ruin-clipped dividend source: three-channel finite-mesh Itô budget and limits
-- statement:
--   On the actual original UBV Lévy process stopped at the natural bounded ruin clock, establish finite physical-grid signed Ito/Meyer terminal-plus-cash budgets with integrable centred Gaussian, compensated small-jump and large-jump martingale limits and nonpositive generator and dividend residual limits. The finite-grid martingales have genuinely zero mean on the original probability space, and their common diagonal converges almost surely. The already-Proved original three-channel assembly theorem then yields the compact stopped signed witness, without assuming the desired budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_bounded_ruinclock_finite_mesh_threechannel_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P) :
    ∃ (Mseq Gseq Hseq : ℕ → Ω → ℝ)
      (Mc Ms Ml G H : Ω → ℝ),
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧ Integrable H P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, ∀ j : ℕ,
        Term ω + Cash ω ≤ w x + Mseq j ω + Gseq j ω + Hseq j ω) ∧
      (∀ᵐ ω ∂P, ∀ j : ℕ, Gseq j ω + Hseq j ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun j => Mseq j ω) atTop (𝓝 (Mc ω + Ms ω + Ml ω)) ∧
        Tendsto (fun j => Gseq j ω) atTop (𝓝 (G ω)) ∧
        Tendsto (fun j => Hseq j ω) atTop (𝓝 (H ω))) := by sorry
