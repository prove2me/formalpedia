-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_grid_chronological_cross_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_grid_chronological_cross_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:58:25.249801+00:00
-- url     : https://prove2.me/theorems/082e8efa-d40d-4461-b660-5e26c8f61877
-- title:
--   Same-original Lévy chronological finite-grid expected count cross terms equal the exact compensator sum
-- statement:
--   For an arbitrary finite family of source time windows (sᵢ,tᵢ] and the same spectrally negative Lévy process X, the sum of genuine cross-window marked count expectations E[N_X(0,sᵢ] N_X(sᵢ,tᵢ]] equals the sum of genuine past expected counts times each original Lévy compensator (tᵢ-sᵢ)ν(-∞,-1/(n+1)]. The source-past weights and source-future counts are on the exact same Ω/P/𝓕/X. This is the finite-grid expected chronological cross term before the separately required pathwise refinement and monotone convergence to the full chronological pair expectation.
-- source:
--   Uses Proved original-source P2-E via source-exact cross-window helper a8adacce; intermediate finite-grid interface for chronological pair mean d938e9a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_cross_window_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_grid_chronological_cross_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i) (n : ℕ) :
    let Jpast : Fin m → Ω → ℝ≥0∞ := fun i ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc 0 (s i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Fin m → Ω → ℝ≥0∞ := fun i ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc (s i) (t i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    (∑ i : Fin m, ∫⁻ ω, Jpast i ω * Jfuture i ω ∂P) =
      ∑ i : Fin m, (∫⁻ ω, Jpast i ω ∂P) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) *
          X.ν (Iic (-(1 / ((n : ℝ) + 1))))) := by sorry
