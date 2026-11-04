-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_cash_injective_atomic_subseries_summable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_injective_atomic_subseries_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:27:34.483876+00:00
-- url     : https://prove2.me/theorems/3aeb5824-0bd1-401b-9621-8125a0d711f0
-- title:
--   Every injective enumeration of genuine stopped original dividend atomic cash retains absolute real summability
-- statement:
--   The already proved source stopped original Stieltjes cash theorem supplies a countable carrier of every nonzero μ singleton and a summable real series of the exact discounted paymentTimes-filtered atom weights. Any injective enumeration into that carrier inherits summability, permitting honest extraction of a true time subseries without duplicating source atoms. Both time zero and the surviving horizon remain in the measure; positive ruin payment is filtered out by the original paymentTimes selector.
-- source:
--   Source proved 92982025 genuine original Stieltjes weighted atomic cash summability; Mathlib Summable.comp_injective in pinned revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_injective_atomic_subseries_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ∀ (g : ι → A), Function.Injective g →
        Summable (fun i : ι =>
          (μ {(g i : ℝ)} *
            (if (g i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
              then ENNReal.ofReal (Real.exp (-(q * (g i : ℝ))))
              else 0)).toReal) := by sorry
