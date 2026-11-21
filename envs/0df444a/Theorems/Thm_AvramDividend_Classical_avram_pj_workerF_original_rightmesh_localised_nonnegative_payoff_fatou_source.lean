-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_original_rightmesh_localised_nonnegative_payoff_fatou_source
-- name    : AvramDividend.Classical.avram_pj_workerF_original_rightmesh_localised_nonnegative_payoff_fatou_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:09:37.543222+00:00
-- url     : https://prove2.me/theorems/6c1b23ee-1844-4797-a87b-2c1ac17a47c9
-- title:
--   Original right-mesh stopped nonnegative localiser expectation budgets and true payoff liminf source
-- statement:
--   For the genuine original bounded ruin-stopped right-mesh clock ρ(k,m)=min(τ,σ_k+1/(m+1)), caplinear discounted postpayment terminal and complete original inclusive dividend Stieltjes cash payoff Approx(m), construct for each k,m an authentic sequence of measurable nonnegative ENNReal localised stopped rewards A_j. Every localised true original-model process must have expected cost ≤ENNReal.ofReal(w x), justified by actual optional sampling of its centred compensated Gaussian/full negative jump martingales and nonpositive generator and full diffuse-and-atomic dividend correction. The original exact payoff ENNReal.ofReal Approx must be almost surely at most the liminf of the localised A_j, including cash at time zero, all off-grid right dividend atoms and ruin contact. This source is the authentic localising proof obligation and avoids assuming existence of a globally integrable stopped martingale at the full clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_original_rightmesh_localised_nonnegative_payoff_fatou_source
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
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k,
      let ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
        min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      let Approx : ℕ → Ω → ℝ := fun m ω =>
        Real.exp (-(q * (ρ m ω : ℝ))) *
          (let V : ℝ → ℝ := fun z =>
             if ENNReal.ofReal z ≤ C then w z
             else w C.toReal + (z - C.toReal)
           V (if ρ m ω = 0 ∨
               (ρ m ω : ℝ≥0∞) < ruinTime X x D ω then
                x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
              else riskProcess X x D (ρ m ω) ω)) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      (∀ m, ∃ A : ℕ → Ω → ℝ≥0∞,
        (∀ j, Measurable (A j)) ∧
        (∀ j, (∫⁻ ω, A j ω ∂P) ≤ ENNReal.ofReal (w x)) ∧
        (∀ᵐ ω ∂P, ENNReal.ofReal (Approx m ω) ≤
          liminf (fun j => A j ω) atTop)) := by sorry
