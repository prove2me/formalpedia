-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_original_rightmesh_cofinal_localiser_stopped_reward_budgets
-- name    : AvramDividend.Classical.avram_pj_workerF_original_rightmesh_cofinal_localiser_stopped_reward_budgets
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:14:32.528889+00:00
-- url     : https://prove2.me/theorems/f66f5747-93f4-4636-941f-e5174812fb42
-- title:
--   Actual original caplinear inclusive-cash stopped reward at a cofinal sequence of integrable stochastic localisers
-- statement:
--   For every original bounded physical rightmesh clock rho(k,m), construct genuinely adapted increasing right-continuous stopping localisers S_j with S_j going to infinity almost surely, so that the clipped original clock localClock_j=min(rho(k,m),S_j) carries the exact original discount*caplinear terminal plus full inclusive paymentTimes/Iic Stieltjes dividend cash LocalReward_j. Show measurability of each nonnegative ENNReal ofReal LocalReward_j and a uniform per-j expectation <=ENNReal.ofReal(w x), using the authentic stopped Meyer-Ito formula for X and D and full compensated Gaussian/negative jump channels, HJB, diffuse/atomic dividend losses and ruin. The eventual exact reward identity at the bounded clock is independently Proved by avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact, so a.e. liminf follows without any global integrable martingale or loss of offgrid dividend atoms. This is the actual remaining localised stochastic budget source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_original_rightmesh_cofinal_localiser_stopped_reward_budgets
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
      (∀ m, ∃ S : ℕ → Ω → ℝ≥0∞,
        (∀ j, IsStoppingTime 𝓕.rightCont (S j)) ∧
        (∀ ω, Monotone (fun j => S j ω)) ∧
        (∀ᵐ ω ∂P, (⨆ j : ℕ, S j ω) = ⊤) ∧
        (let localClock : ℕ → Ω → ℝ≥0 := fun j ω =>
          (min (ρ m ω : ℝ≥0∞) (S j ω)).toNNReal
         let V : ℝ → ℝ := fun z =>
           if ENNReal.ofReal z ≤ C then w z
           else w C.toReal + (z - C.toReal)
         let LocalReward : ℕ → Ω → ℝ := fun j ω =>
           Real.exp (-(q * (localClock j ω : ℝ))) *
             V (if localClock j ω = 0 ∨
                 (localClock j ω : ℝ≥0∞) < ruinTime X x D ω then
                   x + X.X (localClock j ω) ω -
                     rightLimit D (localClock j ω) ω
                 else riskProcess X x D (localClock j ω) ω) +
           (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
               Iic (localClock j ω : ℝ),
             ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
         (∀ j, Measurable (fun ω => ENNReal.ofReal (LocalReward j ω))) ∧
         (∀ j, (∫⁻ ω, ENNReal.ofReal (LocalReward j ω) ∂P) ≤
           ENNReal.ofReal (w x)))) := by sorry
