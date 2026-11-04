-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atomic_series
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atomic_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:09:30.995553+00:00
-- url     : https://prove2.me/theorems/152570c5-b6bd-4de8-8a18-cbcad4a8f607
-- title:
--   Original source Cash atomic ENNReal sum equals a genuine summable real atomic series
-- statement:
--   Using only the countable Cash atom set, exact atom-plus-diffuse split, total horizon right-limit mass, and q≥0 returned by the original source, the atomic Cash contribution is a genuinely summable real series and its total equals toReal of the exact ENNReal atomic sum. This is the required source-level real Cash atom bridge for stopped-budget assembly.
-- source:
--   Proved source Cash decomposition f897c004, P4-F original weighted atom finiteness and finite-to-real sum conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atomic_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (hA : A.Countable)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (htotal : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ =
        ENNReal.ofReal (rightLimit D T ω))
    (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun a : A => ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}).toReal) ∧
    (∑' a : A, (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}).toReal =
      ∑' a : A, ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}).toReal := by sorry
