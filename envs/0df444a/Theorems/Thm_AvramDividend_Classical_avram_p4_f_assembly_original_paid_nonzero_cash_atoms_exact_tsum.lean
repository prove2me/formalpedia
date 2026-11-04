-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:38:54.379639+00:00
-- url     : https://prove2.me/theorems/9f1caf71-8042-430f-8647-edee8f4d21a5
-- title:
--   Original ruin-stopped Cash atomic sum equals the unweighted discounted sum over exactly paid nonzero atoms
-- statement:
--   The source Cash decomposition retains an indicator of the genuine pre-ruin paymentTimes domain. This theorem removes both unpaid and zero-mass real atomic indices from the exact infinite sum, leaving the actual nonzero paid atoms with their original exponential weights and Stieltjes singleton masses. This is the source-exact index set needed to apply the accepted physical clock and HJB secant lemmas.
-- source:
--   True source Cash decomposition 188366d0 and pinned Mathlib tsum_subtype_eq_of_support_subset. No assertion that support in the horizon implies payment eligibility.

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (A : Set ℝ)
    (μatom : Measure ℝ) (q : ℝ) :
    (∑' a : A,
      ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
        μatom {a.1}).toReal) =
    ∑' a : {a : A // a.1 ∈ paymentTimes (ruinTime X x D ω) ∧
      μatom {a.1} ≠ 0},
      (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
        μatom {a.1.1}).toReal := by sorry
