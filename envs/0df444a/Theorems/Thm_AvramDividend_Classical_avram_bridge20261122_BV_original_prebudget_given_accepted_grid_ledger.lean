-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_BV_original_prebudget_given_accepted_grid_ledger
-- name    : AvramDividend.Classical.avram_bridge20261122_BV_original_prebudget_given_accepted_grid_ledger
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:11:13.976671+00:00
-- url     : https://prove2.me/theorems/7012a6fd-1e14-4590-9109-b4fe852dbf95
-- title:
--   Physical BV stopped HJB prebudget conditional on three verified discounted finite-step and secant cash ledger interfaces
-- statement:
--   Same physical original BV positive-horizon stopped cash and post-payment terminal bound. The child assumes three universally reusable proved discrete HJB/cash ledger interfaces (mean step-HJB budget, deterministic residual cash budget, secant ledger with signed cell error). It still needs to construct the authentic physical grid approximations, establish the stepwise generator/Itô mean bounds, and pass to the stopped Stieltjes cash.
-- source:
--   Original connected BV prebudget a19d8b28 and remote-Proved finite-grid heads 43b2c10d, 9d929282, 23e21299, preserving the original cash and terminal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261122_BV_original_prebudget_given_accepted_grid_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hGridLedger : (∀ [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (u preDividend cash : ℕ → Ω → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0) (x : ℝ)
    (hu0 : ∀ ω, u 0 ω = x)
    (hAfter : ∀ k ω, u (k + 1) ω = preDividend k ω - cash k ω)
    (hCashNonneg : ∀ k ω, 0 ≤ cash k ω)
    (hwCont : ∀ k ω, ContinuousOn w
      (Icc (preDividend k ω - cash k ω) (preDividend k ω)))
    (hwDiff : ∀ k ω, DifferentiableOn ℝ w
      (interior (Icc (preDividend k ω - cash k ω) (preDividend k ω))))
    (hwGrad : ∀ k ω, ∀ y ∈
      interior (Icc (preDividend k ω - cash k ω) (preDividend k ω)),
        1 ≤ deriv w y)
    (n : ℕ)
    (hCashInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k ω) P)
    (hTerminalInt : Integrable (fun ω =>
      Real.exp (-(q * s n)) * w (u n ω)) P)
    (hStepInt : ∀ k, Integrable (fun ω =>
      Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω)) P)
    (hStep : ∀ k, (∫ ω,
      Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω) ∂P) ≤ 0)
    (hTerminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P),
(∫ ω, ∑ k ∈ Finset.range n,
      Real.exp (-(q * s (k + 1))) * cash k ω ∂P) ≤ w x) ∧
      (∀ (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ)
    (hResidual : (∑ k ∈ Finset.range n,
      (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
        Real.exp (-(q * s k)) * w (u k))) ≤ 0)
    (hTerminal : 0 ≤ w (u n)),
(∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) ≤
      w (u 0)) ∧
      (∀ (w : ℝ → ℝ) (u preDividend cash err : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)) + err k)
    (n : ℕ),
(∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) +
        Real.exp (-(q * s n)) * w (u n) ≤
      w (u 0) +
        ∑ k ∈ Finset.range n,
          (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
            Real.exp (-(q * s k)) * w (u k)) +
      ∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * err k)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
