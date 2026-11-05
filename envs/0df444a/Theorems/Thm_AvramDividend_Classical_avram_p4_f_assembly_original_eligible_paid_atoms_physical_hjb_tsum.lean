-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_eligible_paid_atoms_physical_hjb_tsum
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_eligible_paid_atoms_physical_hjb_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:56:43.920345+00:00
-- url     : https://prove2.me/theorems/3c05921a-622f-4ebe-bbd5-82f3ec7f7f5a
-- title:
--   True paid nonzero original Stieltjes atoms satisfy the discounted HJB ENNReal total cash bound
-- statement:
--   For original X and original dividend D, the actual paid nonzero singleton masses from a finite-horizon Stieltjes decomposition are strictly eligible original payment times. Consequently their discounted extended-real cash sum is bounded by the corresponding HJB value-loss sum. The source mass and eligibility assumptions are discharged from the accepted physical atom theorem, avoiding an artificial L1/summability assumption.
-- source:
--   Original hRight and hsplit, accepted physical atom c5fbf7f7, accepted ENNReal summation 47c5a92b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_eligible_paid_atoms_physical_hjb_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ u : ℝ≥0, u ≤ T →
      μatom {(u : ℝ)} =
        ENNReal.ofReal (rightLimit D u ω - D u ω)) :
    let E : Set ℝ := {t | t ∈ A ∧
      t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
    (∑' a : E,
      ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
    ∑' a : E,
      ENNReal.ofReal (Real.exp (-(q * a.1))) *
        ENNReal.ofReal
          (w (riskProcess X x D (Real.toNNReal a.1) ω) -
            w (riskProcess X x D (Real.toNNReal a.1) ω -
              (rightLimit D (Real.toNNReal a.1) ω -
                D (Real.toNNReal a.1) ω))) := by sorry
