-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atom_series_plus_diffuse
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atom_series_plus_diffuse
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:49:54.819274+00:00
-- url     : https://prove2.me/theorems/bbc9d963-5dc3-4c7c-8640-7b7fb752820a
-- title:
--   Exact original stopped Cash in real atomic series plus diffuse Stieltjes contribution
-- statement:
--   When the source original ruin-stopped discounted Cash is decomposed exactly into its atomic ENNReal total plus the non-atomic Stieltjes part and the atomic total is finite, the atomic component is a summable real series and the full exact Cash equals that real series plus the original diffuse Cash. This performs the required legitimate ENNReal-to-real series passage without omitting continuous or singular-continuous dividend mass.
-- source:
--   Source stopped Cash atomic plus diffuse theorem f897c004 and P4-F finite ENNReal real-atom converter 06ecfaee, now Proved by remote accepted submission fffa2944.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atom_series_plus_diffuse
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (ρ : ℝ≥0∞) (q : ℝ) (T : ℝ≥0)
    (A : Set ℝ) (μatom μdiffuse : Measure ℝ)
    (f : ℝ → ℝ≥0∞)
    (hfinite : (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤)
    (hCashEq :
      (∫⁻ s in paymentTimes ρ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
      (∑' a : A, f a.1 * μatom {a.1}).toReal +
        (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) :
    Summable (fun a : A => (f a.1 * μatom {a.1}).toReal) ∧
      (∫⁻ s in paymentTimes ρ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
      (∑' a : A, (f a.1 * μatom {a.1}).toReal) +
        (∫⁻ s : ℝ, f s ∂μdiffuse).toReal := by sorry
