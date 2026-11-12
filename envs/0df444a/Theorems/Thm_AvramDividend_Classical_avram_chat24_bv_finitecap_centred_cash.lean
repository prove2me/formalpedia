-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_finitecap_centred_cash
-- name    : AvramDividend.Classical.avram_chat24_bv_finitecap_centred_cash
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T13:28:20.742856+00:00
-- url     : https://prove2.me/theorems/2ee0a416-57f4-4989-950a-a0e286d2e712
-- title:
--   Finite-cap BV centred cash estimate without a raw generator-grid budget
-- statement:
--   Let X be a spectrally negative Levy process satisfying the standing assumptions, with bounded variation and arbitrary negative-jump intensity, under a finite positive reserve cap C. Let q>0 and let D be an capped admissible dividend strategy with nonnegative initial capital x within the cap. Let w be continuous on the nonnegative half-line and C1 on the positive interior of the cap, zero below zero, nonnegative at zero and on surviving controlled reserves, with integrable generator, generator inequality (Gamma-q)w<=0, derivative at least one, and the stated dividend-jump secant inequality.
--
--   For a deterministic horizon T>0 set delta_n=T/(n+2). Let A_n be the discounted Stieltjes dividends paid strictly before T-delta_n, under the original payment-time and ruin conventions, including the time-zero atom. Let V_T equal exp(-qT)w(U_T) on survival to T and zero otherwise, where U is the original controlled reserve. Put F_n=A_n+V_T.
--
--   There exist real random variables M_n and E_n and positive real numbers eta_n tending to zero such that M_n is integrable with expectation zero, the positive part E_n^+ is integrable, and
--
--   $$
--   F_n\le w(x)+M_n+E_n^+\quad\hbox{almost surely},\qquad
--   \mathbb E[E_n^+]\le\eta_n.
--   $$
--
--   This auxiliary estimate supports the stopped expected-dividend verification bound. Its conclusion retains no raw, unlocalised signed generator-grid budget. Formalization note: A_n is represented by the toReal of the original nonnegative Stieltjes integral; no process, filtration, admissibility or ruin convention is replaced.
-- source:
--   Case-specific source-faithful auxiliary for Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4; https://arxiv.org/abs/math/0702893. Excluded-middle decomposition of existing no-raw-budget theorem 2ea49e60-88d3-4b70-805f-31c906df8510. The corrected parent route splits finite cap, top cap with finite activity, and top cap with infinite activity. This declaration asserts no raw signed generator-grid term and is not a proof of the older stronger b0dd41fe intermediate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_bv_finitecap_centred_cash
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
    (T : ℝ) (hT : 0 < T)
    (hFinite : C ≠ ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + M n ω + max (Err n ω) 0) ∧
      (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n) := by sorry
