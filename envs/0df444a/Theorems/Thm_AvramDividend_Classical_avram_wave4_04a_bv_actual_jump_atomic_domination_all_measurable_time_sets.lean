-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:19:58.556182+00:00
-- url     : https://prove2.me/theorems/6db7ca71-b2a6-468c-9020-c8178e8d9dd3
-- title:
--   The genuine BV Lévy source jump-atom measure is dominated by its own residual Stieltjes measure on every Borel time set
-- statement:
--   On a single probability-one event for the actual original source BV process X, there exists the actual path residual Stieltjes function F(t)=t*d−X_t. Simultaneously for every Borel set B of times, the complete countable sum of genuine downward source jump magnitudes at positive times in B is bounded by F.measure B. This is source-path atomic measure domination on arbitrary time sets, not just intervals. It is a pathwise precursor for stopped/reserve-dependent BV jump integrals; it proves no Poisson count law, Campbell formula, compensator, or absence of continuous residual mass.
-- source:
--   Canonical Proved actual BV source Stieltjes singleton atom theorem 0c2826fa-5cd3-4dcb-bef0-9a029879d9b2. Apply Mathlib ENNReal.tsum_eq_iSup_sum and finite singleton measure additivity to each finite subset of B, then measure_mono. Original sample ω and original X only.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ (B : Set ℝ≥0), MeasurableSet B →
        (∑' (u : ℝ≥0),
          if 0 < u ∧ u ∈ B then
            ENNReal.ofReal (Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
          else 0) ≤ F.measure B) := by sorry
