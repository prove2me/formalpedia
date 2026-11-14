-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_any_cofinal_negative_mark_compensator_fixed_compact_integrals_eventually_identical
-- name    : AvramDividend.Classical.avram_bva_a22_original_any_cofinal_negative_mark_compensator_fixed_compact_integrals_eventually_identical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:34:18.04589+00:00
-- url     : https://prove2.me/theorems/241eab7e-b245-4060-a05a-4766abda9e9a
-- title:
--   Original negative-mark compensated integrals on any fixed stopped interior compact are literally unchanged by arbitrary cofinal spatial band masks for all large rows
-- statement:
--   For the actual original filtered spectrally negative Lévy X, admissible dividend D, discounted negative-mark jump candidate increment, exact pre-right-payment left-limit reserve, genuine ruin stop and any prescribed arbitrary cofinal interior spatial bands, fix an interior reserve compact [c,d]. Prove there is one deterministic index N such that for every later spatial row, every fixed horizon S and every measure on the actual time-path-mark product, the Bochner integral of the original negative-mark kernel with BOTH the fixed compact and the spatial-band mask is exactly equal to the integral with only the fixed compact mask. The Proved original stopped compact-coverage theorem makes the two source integrands literally pointwise equal on all product tuples, so no global integrability/finite intensity, fast spatial rate, or replacement process is needed for this fixed-compact identity. This is the measure-level source alignment prerequisite for eventual arbitrary-band negative compensated mark convergence; the random-boundary spatial tail remains separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_ruinstopped_prepayment_compact_allband
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_any_cofinal_negative_mark_compensator_fixed_compact_integrals_eventually_identical
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0)
      (μ : Measure ((ℝ≥0 × Ω) × ℝ)),
      (∫ p, if
        (((p.1.1 : ℝ≥0∞) ≤ min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) ∧
          Y p.1.1 p.1.2 ∈ Icc (a n) (b n)) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0 ∂μ) =
      (∫ p, if
        ((p.1.1 : ℝ≥0∞) ≤ min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0 ∂μ) := by sorry
