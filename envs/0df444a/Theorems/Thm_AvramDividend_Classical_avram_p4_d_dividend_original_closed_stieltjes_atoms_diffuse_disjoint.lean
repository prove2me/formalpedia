-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:35:12.998532+00:00
-- url     : https://prove2.me/theorems/5126bd4b-9a36-41cf-a2c0-59ad5bb10d18
-- title:
--   Original closed Stieltjes right-atomic and diffuse measures have disjoint carriers, exact endpoints and full mass
-- statement:
--   From the actual original dividendMeasure restricted to the entire closed [0,T] window, take the source-proved countable Dirac right-atom decomposition and atomless remainder. The atomless remainder gives zero measure to the same countable atomic carrier, while the atomic component has zero measure outside it. Thus there is no overlap when using the corresponding atom and diffuse payment corrections. Preserve the original singleton μ{t}=ofReal(D_{t+}-D_t), including t=0 and the horizon-right-payment atom, and the full μ(univ)=ofReal(D_{T+}) mass; singular-continuous dividends remain in the diffuse component. This does not assume finite jump activity or an absolutely continuous control.
-- source:
--   Original Avram source dividendMeasure/rightLimit definitions; Proved d19177af exact Stieltjes decomposition; pinned Mathlib Set.Countable.measure_zero for NullSingletonClass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
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
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by sorry
