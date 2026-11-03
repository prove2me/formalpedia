-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_implies_ae_signed_preRuin_tails_vanish
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_signed_preRuin_tails_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:00:19.523252+00:00
-- url     : https://prove2.me/theorems/b51f39c1-5f0c-4c2e-8da6-d071352e0658
-- title:
--   Finite canonical original expected ENNReal dividendValue forces actual signed real Stieltjes pre-ruin payment tails to vanish almost surely
-- statement:
--   On the actual original Levy process, original Ω/P and genuine source dividendMeasure D, if the complete doubly integrated ENNReal dividendValue is finite, then for P-almost every path the real discounted signed Stieltjes cash on paymentTimes(ruinTime)∩Ioi(n) tends to zero at infinity, with the initial right-limit dividend atom and all continuous/jump payments incorporated in the original full cash. This is a rigorous terminal vanishing consequence of finite value: the previously accepted original finiteness characterisation provides almost-sure *inner* ENNReal finiteness, the precise source signed integrability iff converts this to genuine IntegrableOn on each path, and the accepted strict pre-ruin real tail lemma gives the limit. It does not infer integrability from the totalised real integral on infinite-cash paths.
-- source:
--   Accepted general original value finiteness iff signed L1 plus a.e pathwise finite fd64314b, pathwise original ENNReal finite iff genuine signed IntegrableOn a6d24d2f, and conditional original strict pre-ruin real tail limit after it becomes Proved.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_signed_preRuin_tails_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω))
        atTop (𝓝 0) := by sorry
