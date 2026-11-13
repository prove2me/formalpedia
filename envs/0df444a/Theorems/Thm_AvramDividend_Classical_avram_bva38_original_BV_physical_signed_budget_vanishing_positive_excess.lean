-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva38_original_BV_physical_signed_budget_vanishing_positive_excess
-- name    : AvramDividend.Classical.avram_bva38_original_BV_physical_signed_budget_vanishing_positive_excess
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T11:15:48.00819+00:00
-- url     : https://prove2.me/theorems/0c4f953b-9598-48d3-84ff-4c30577c0ebd
-- title:
--   Original infinite-activity BV integrable physical signed budget with vanishing positive excess
-- statement:
--   Construct along a cofinal strict inner horizon grid one integrable signed budget N_m on the original Lévy source, with E[N_m]<=0, and show the positive excess max(F_m - w(x) - N_m,0) is integrable with expected value tending to zero. The signed budget must come from the original compensated negative-jump gains and nonpositive generator/Stieltjes drift. The residual is the positive physical cash-plus-terminal ledger discrepancy and must control zero-time right dividends, ruin contacts and infinitely many small marks. Existing Proved abstract two-error positive-L1 lemmas can be applied after establishing the actual physical ledger.
-- source:
--   Physical positive-excess bottleneck of bva36, matching proved bv_strict10_two_positive_errors_exact_excess_L1_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva38_original_BV_physical_signed_budget_vanishing_positive_excess
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
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ N : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable
        (fun ω => max (F m ω - (w x + N m ω)) 0) P) ∧
      Tendsto (fun m =>
        ∫ ω, max (F m ω - (w x + N m ω)) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
