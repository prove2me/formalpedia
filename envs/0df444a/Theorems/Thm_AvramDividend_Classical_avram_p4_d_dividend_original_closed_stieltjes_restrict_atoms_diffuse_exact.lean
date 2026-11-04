-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:37:12.430011+00:00
-- url     : https://prove2.me/theorems/8d308a32-02f6-40e6-85fc-d5dc97fa3584
-- title:
--   Original closed Stieltjes atom and diffuse component equal literal restrictions to disjoint carriers
-- statement:
--   For the actual source closed original dividendMeasure on [0,T], construct the countable right-atomic carrier A and the true atomless remainder. Prove exact measure identities μ.restrict A = μatom and μ.restrict Aᶜ = μdiffuse, using the source atom decomposition, zero mass outside atomic carrier, and countable null sets under the genuine atomless measure. Consequently a split of any integrable dividend correction over these restrictions cannot double count an atom or omit singular continuous mass. The exact original singleton rightLimit payment at t=0 and t=T and cumulative total mass remain included.
-- source:
--   Source-proved d19177af original complete atom/diffuse Stieltjes decomposition; Mathlib mem_ae_iff, Measure.restrict_eq_self_of_ae_mem, Measure.restrict_add, Measure.restrict_eq_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μ.restrict A = μatom ∧
      μ.restrict Aᶜ = μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by sorry
