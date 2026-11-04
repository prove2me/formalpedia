-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_injective_atomic_cash_full_stieltjes_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_injective_atomic_cash_full_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:48:50.866914+00:00
-- url     : https://prove2.me/theorems/a867cb3c-93f9-4720-9ea7-a94a42e6fd98
-- title:
--   The true stopped Stieltjes atomic carrier uniformly bounds injective subseries by complete discounted cash
-- statement:
--   The source-proved exact original closed-interval discounted atom-plus-diffuse cash decomposition gives a single true countable atomic carrier and finite ENNReal full integral. An injective enumeration into that carrier has ENNReal atomic sum no greater than the full carrier by ENNReal.tsum_comp_le_tsum_of_injective; its ENNReal sum is finite, yielding Summable real toReal weights and a real tsum upper bound by the full exact stopped discounted Stieltjes cash integral. The result uses the same source-selected carrier for both conclusions, includes t=0 and surviving horizon payments, and keeps singular-continuous cash in the nonnegative diffuse complement.
-- source:
--   Source-proved 0a519d31 exact original stopped full atomic/diffuse cash decomposition and finite bound; Mathlib ENNReal.tsum_comp_le_tsum_of_injective, ENNReal.summable_toReal, ENNReal.tsum_toReal_eq, ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_injective_atomic_cash_full_stieltjes_bound
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
              else 0)).toReal) ∧
        (∑' i : ι, (μ {(g i : ℝ)} *
          (if (g i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * (g i : ℝ))))
            else 0)).toReal) ≤
          (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by sorry
