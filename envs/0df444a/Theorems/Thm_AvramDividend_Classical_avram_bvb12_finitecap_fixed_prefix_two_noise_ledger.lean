-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb12_finitecap_fixed_prefix_two_noise_ledger
-- name    : AvramDividend.Classical.avram_bvb12_finitecap_fixed_prefix_two_noise_ledger
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T13:06:20.112534+00:00
-- url     : https://prove2.me/theorems/168086af-6852-42f5-abcf-b49c8cff991e
-- title:
--   Finite-cap BV fixed original cash prefix: two-noise compensated ledger
-- statement:
--   For each original strict dividend cash prefix before T, a finer auxiliary mesh yields a source-exact stopped BV drift, jump and dividend ledger. The original F is integrable, with centred integrable compensated marked-jump errors, integrable remainder tending to zero in mean, and an a.e. upper bound. Handle the initial right payment, continuous singular dividends including zero reserves, ruin mark, terminal T and HJB sign under the actual Standing finite-activity source. Independent of the parent 843d4165 and its finite-cap split.
-- source:
--   Avram-Palmowski-Pistorius 2007 Prop 4(i), Eq (5.13); Protter Thm 31 FV chain; Kyprianou Thm 4.4 compensated jump identity. BV-B research/avram_bvb_20261112/PLAN.md.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb12_finitecap_fixed_prefix_two_noise_ledger
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
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapFinite : C ≠ ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, ∃ (M E : ℕ → Ω → ℝ),
      Integrable (F n) P ∧
      (∀ k, Integrable (M k) P) ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, (∫ ω, M k ω ∂P) = 0) ∧
      (∀ k, ∀ᵐ ω ∂P, F n ω ≤ w x + M k ω + E k ω) ∧
      Tendsto (fun k => ∫ ω, E k ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
