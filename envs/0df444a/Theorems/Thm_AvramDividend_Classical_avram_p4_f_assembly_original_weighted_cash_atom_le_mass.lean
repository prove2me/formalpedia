-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_weighted_cash_atom_le_mass
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_weighted_cash_atom_le_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:52:45.635812+00:00
-- url     : https://prove2.me/theorems/c1b350b8-0d8b-412e-bd3a-ad5d271f9867
-- title:
--   Exact original Cash discounted atoms dominated by atomic masses, all source indices
-- statement:
--   For every index in the exact original Cash atom subtype A, the discounted payment-time-selector atom is bounded by its original atomic singleton mass. Inside the physical horizon this follows from q≥0 and exp(-q*s)≤1; outside the horizon source restricted atomic mass vanishes. Thus no unsupported assumption that every arbitrary A-index is a valid payment time is needed.
-- source:
--   Proved original Cash atom split f897c004; P4-F Proved physical-support target 7293bcac and Proved nonnegative-time discount target 290e0cc2; pinned Mathlib gcongr. Previous publication attempt suffered a transient transport ConnectionTerminated while importing the already-Proved discount target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_weighted_cash_atom_le_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (q : ℝ) (hq : 0 ≤ q) (A : Set ℝ) :
    ∀ a : A,
      (if a.1 ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) * μatom {a.1} ≤ μatom {a.1} := by sorry
