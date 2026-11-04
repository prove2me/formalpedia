-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:43:56.259533+00:00
-- url     : https://prove2.me/theorems/aa561d4b-57e2-4163-a4d3-90c08988780c
-- title:
--   True original stopped Cash is the summable discounted series over exactly paid nonzero right atoms plus diffuse Stieltjes cash
-- statement:
--   Compose the original full Cash countable atom-plus-diffuse source decomposition with exact reindexing to paid nonzero atoms. The result preserves the genuine original right-limit singleton mass formula, a countable real index set, and summability of the unweighted real atomic series on exactly eligible payment times.
-- source:
--   Accepted 188366d0 original Cash decomposition and paid effective support reindexer (publication pending).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_full_real_decomposition_with_rightjump
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atoms_exact_tsum
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧ μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      Summable (fun a : {a : A //
        a.1 ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {a.1} ≠ 0} =>
        (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
          μatom {a.1.1}).toReal) ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
        (∑' a : {a : A //
          a.1 ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {a.1} ≠ 0},
          (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
            μatom {a.1.1}).toReal) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * s))) else 0)
            ∂μdiffuse).toReal := by sorry
