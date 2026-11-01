-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:15:39.453211+00:00
-- url     : https://prove2.me/theorems/0c2826fa-5cd3-4dcb-bef0-9a029879d9b2
-- title:
--   Actual BV original Lévy downward jump magnitudes are singleton masses of its residual Stieltjes measure
-- statement:
--   For almost every original BV source sample ω, the true residual Y_t=t d-X_t is monotone and gives a right-continuous Stieltjes function F with F_t=Y_t. At every strictly positive original time t, the singleton atom F.measure({t}) equals ofReal(X_{t-}-X_t), precisely the magnitude of the actual downward source jump, with no equal-law construction or auxiliary Poisson space. This does not assert that the measure is purely atomic, that its jump counts are Poisson, or any predictable compensator.
-- source:
--   Canonical original source BV residual a.e. monotonicity f6cc1059-e8ca-403e-8d73-71a139d3dc4c; SpectrallyNegativeLevy pathwise rightCont and leftLim; pinned StieltjesFunction.measure_singleton, Monotone.stieltjesFunction_eq, ContinuousWithinAt.rightLim_eq, leftLim_eq_of_tendsto, nhdsLT_neBot_of_exists_lt. This is a genuinely source-mark/measure atom link distinct from the interval mass representation.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ t : ℝ≥0, 0 < t →
        F.measure {t} =
          ENNReal.ofReal (Function.leftLim
            (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)) := by sorry
