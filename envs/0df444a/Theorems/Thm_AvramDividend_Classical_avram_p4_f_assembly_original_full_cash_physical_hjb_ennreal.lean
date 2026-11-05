-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_cash_physical_hjb_ennreal
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_full_cash_physical_hjb_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:05:02.602387+00:00
-- url     : https://prove2.me/theorems/d62e1beb-e8f3-4778-bf65-0ace3de669ff
-- title:
--   Original full stopped Stieltjes atomic cash has actual HJB value-loss ENNReal bound
-- statement:
--   For original X,D and original jump secant, decompose the physical finite-horizon dividend measure into true countable paid right atoms and diffuse measure. The actual paid discounted atomic Cash has an extended-real upper bound by the corresponding original postdividend HJB losses without external singleton-mass, eligibility, or summability assumptions. This uses only previously accepted original source theorems.
-- source:
--   Accepted physical source cash decomposition aa561d4b, physical paid-atom eligibility c5fbf7f7, and source jump HJB ENNReal summation 47c5a92b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_full_cash_physical_hjb_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧ μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∑' a : {t : ℝ | t ∈ A ∧
          t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0},
        ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
      ∑' a : {t : ℝ | t ∈ A ∧
          t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0},
        ENNReal.ofReal (Real.exp (-(q * a.1))) *
          ENNReal.ofReal
            (w (riskProcess X x D (Real.toNNReal a.1) ω) -
              w (riskProcess X x D (Real.toNNReal a.1) ω -
                (rightLimit D (Real.toNNReal a.1) ω -
                  D (Real.toNNReal a.1) ω))) := by sorry
