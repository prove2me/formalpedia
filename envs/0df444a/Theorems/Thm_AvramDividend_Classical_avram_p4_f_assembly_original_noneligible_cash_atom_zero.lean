-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_noneligible_cash_atom_zero
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_noneligible_cash_atom_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:40:39.581888+00:00
-- url     : https://prove2.me/theorems/b960c55b-c93a-400d-98e7-d956f54c9ef3
-- title:
--   Original cash atomic term vanishes for every out-of-horizon or nonpayment index
-- statement:
--   The exact original countable Cash atomic sum includes a set of indices that may contain points outside the stopped physical horizon and times not eligible for payment. The weighted atomic ENNReal term is identically zero on the union of both ineligible cases, including when the underlying mass is infinite. This isolates precisely the effective physical Cash atoms.
-- source:
--   Original restricted Cash measure decomposition f897c004, proved original atomic support 7293bcac.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_noneligible_cash_atom_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (q a : ℝ)
    (hnot : a ∉ Icc (0 : ℝ) (T : ℝ) ∨
      a ∉ paymentTimes (ruinTime X x D ω)) :
    (if a ∈ paymentTimes (ruinTime X x D ω) then
      ENNReal.ofReal (Real.exp (-(q * a))) else 0) *
      μatom {a} = 0 := by sorry
