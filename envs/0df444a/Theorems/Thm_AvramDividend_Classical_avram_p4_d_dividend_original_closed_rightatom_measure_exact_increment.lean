-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_rightatom_measure_exact_increment
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_rightatom_measure_exact_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:31:02.562884+00:00
-- url     : https://prove2.me/theorems/0944a80d-da0c-4a1f-932e-6b4a7d6f3cf7
-- title:
--   Original closed-window atomic dividend measure has exact rightLimit increment at every payment including endpoints
-- statement:
--   For the source original Stieltjes dividend measure restricted to closed [0,T], the accepted disjoint right-atomic/atomless decomposition gives zero singleton mass to its diffuse component. Thus every actual right-payment singleton mass in the atomic component equals ofReal(rightLimit D t ω - D t ω) for 0 ≤ t ≤ T, including t=0 and t=T, with the full closed-window mass conserved. This supplies the exact source units needed to rewrite discounted atomic Cash sums.
-- source:
--   Accepted original Stieltjes disjoint partition theorem 5126bd4b with source rightLimit increment, pinned Mathlib Measure.add_apply and NullSingletonClass singleton simplification, Avram Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original right-payment atom belongs entirely to the atomic Stieltjes measure. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_rightatom_measure_exact_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) := by sorry
