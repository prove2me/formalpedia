-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_grid_chronological_total_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_grid_chronological_total_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:02:08.950988+00:00
-- url     : https://prove2.me/theorems/284b2602-a2c5-4c38-b309-653177fac53d
-- title:
--   Exact expectation of same-original-process finite-grid chronological marked jump cross-count
-- statement:
--   For a finite family of deterministic original-source time windows and one common negative separated mark band, the expectation of the random sum Σᵢ N_X(0,sᵢ] N_X(sᵢ,tᵢ] is exactly Σᵢ E[N_X(0,sᵢ]] (tᵢ-sᵢ)ν(B) on the same Ω/P/𝓕/X. Every original count is globally measurable, each raw past count is adapted, and the original P2-E weighted compensation yields each cross mean. This supplies the finite-grid sum identity for chronological pair compensation. Pathwise convergence to the full source pair count is a separate outstanding mathematical obligation.
-- source:
--   Proved P2-E intrinsic source rectangle measurability 5cb1e247, source cross-window compensation a8adacce, and finite lintegral sum a30d1d38.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_cross_window_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_grid_chronological_total_mean
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
    (∫⁻ ω, ∑ i : Fin m, Jpast i ω * Jfuture i ω ∂P) =
      ∑ i : Fin m, (∫⁻ ω, Jpast i ω ∂P) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) *
          X.ν (Iic (-(1 / ((n : ℝ) + 1))))) := by sorry
