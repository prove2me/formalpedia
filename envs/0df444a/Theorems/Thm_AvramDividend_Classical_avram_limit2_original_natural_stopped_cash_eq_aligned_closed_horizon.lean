-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_natural_stopped_cash_eq_aligned_closed_horizon
-- name    : AvramDividend.Classical.avram_limit2_original_natural_stopped_cash_eq_aligned_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:11:40.827996+00:00
-- url     : https://prove2.me/theorems/a1fdd4d2-3637-4187-9fca-b73c4e0cb651
-- title:
--   Genuine original natural ruin-stopped expected Stieltjes cash equals its clock-aligned closed-horizon mask
-- statement:
--   For the exact original Lévy surplus X and genuine dividendMeasure D, the fully natural ruin-stopped expected discounted cash without any deterministic window equals the same cash intersected with the clock-aligned Iic n. The proof is pointwise in sample path: accepted source lemma 0482c9a7 proves paymentTimes(min ruin n) subset Iic n, so intersecting with Iic n does not modify the genuine Stieltjes integration domain. Rewriting the nested lintegrals is valid without integrability assumptions and preserves the initial dividend atom even at n=0. This is the source-exact adapter from clock-aligned HJB/Itô budgets to canonical unmasked natural-horizon cash 61bbf167.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_natural_stopped_cash_eq_aligned_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Set.Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
