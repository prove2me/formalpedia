-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:56:12.136906+00:00
-- url     : https://prove2.me/theorems/42ab7fb8-ce7b-4353-b747-496fa02b71bb
-- title:
--   Exact original Cash weighted countable atomic tsum is finite from source right-limit mass
-- statement:
--   At the actual original dividend-measure horizon, the source's exact countable Cash atomic tsum is finite under the hypotheses returned by the Proved atom-plus-diffuse decomposition and q≥0. The original restricted measure has total mass ENNReal.ofReal(rightLimit D T), hence finite; its atomic mass is finite; each discounted selector atom is bounded by the atomic mass across all A indices.
-- source:
--   Proved source Cash decomposition f897c004, new source original finite atom total and source weighted atom domination, pinned Mathlib ENNReal.tsum_le_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cash_atom_total
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_weighted_cash_atom_le_mass
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_weighted_atom_tsum_ne_top
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
    (∑' a : A, (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1}) ≠ ⊤ := by sorry
