-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a428_L2_maximal_envelope_integrability_bridge
-- name    : AvramDividend.Classical.avram_ga_a428_L2_maximal_envelope_integrability_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:50:35.485452+00:00
-- url     : https://prove2.me/theorems/94d3e899-1512-4f7c-b201-433c61c58a08
-- title:
--   An L2 norm majorant yields integrability and a squared expected bound
-- statement:
--   A strongly measurable nonnegative random variable dominated by the square of a function whose L2 norm is at most twice a square-integrable terminal variable is integrable and has at most four times the terminal second moment.
-- source:
--   The L2 maximal norm-to-integral bridge using ENNReal power order, finite norm integral and comparison of nonnegative integrands.

import Mathlib
import Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_readable
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a428_L2_maximal_envelope_integrability_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f g h : Ω → ℝ)
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hf_nn : ∀ ω, 0 ≤ f ω)
    (hfg : ∀ ω, f ω ≤ (g ω)^2)
    (hh : Integrable (fun ω => (h ω)^2) P)
    (hp : eLpNorm g 2 P ≤ 2 * eLpNorm h 2 P) :
    Integrable f P ∧
      (∫ ω, f ω ∂P) ≤ 4 * (∫ ω, (h ω)^2 ∂P) := by sorry
