-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva43_original_BV_physical_signed_two_error_mesh_budget
-- name    : AvramDividend.Classical.avram_bva43_original_BV_physical_signed_two_error_mesh_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T11:38:14.555135+00:00
-- url     : https://prove2.me/theorems/97875d5b-27b7-40ec-b5a4-0c562de05440
-- title:
--   Original infinite-activity BV physical signed grid and two vanishing cell/contact positive errors
-- statement:
--   Construct on the original spectrally negative Lévy X, probability P, filtration and arbitrary admissible singular dividend D, an integrable nonpositive-mean discounted generator plus compensated negative-jump signed budget N_m for each strict uniform horizon index m. Establish the original-path cash-plus-surviving full-T postpayment bound F_m <= w(x)+N_m+positive interior-cell error+positive ruin-contact error. Prove each error's positive part integrable and its expectation tends to zero. This isolates the physical stochastic and Stieltjes ledger in the shape directly handled by Proved bv_strict10_two_positive_errors_exact_excess_L1_tendsto. Handle infinite small-jump activity, time-zero rights, both endpoints, and ruin contacts.
-- source:
--   Two-error physical source exact for bva39 using proved positive excess L1 glue.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva43_original_BV_physical_signed_two_error_mesh_budget
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
    ∃ N ErrCell ErrContact : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable (fun ω => max (ErrCell m ω) 0) P) ∧
      (∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P) ∧
      (∀ m, ∀ᵐ ω ∂P, F m ω ≤ w x + N m ω +
        max (ErrCell m ω) 0 + max (ErrContact m ω) 0) ∧
      Tendsto (fun m => ∫ ω, max (ErrCell m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun m => ∫ ω, max (ErrContact m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
