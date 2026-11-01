-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_interval_measure
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_residual_stieltjes_interval_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:06:32.609294+00:00
-- url     : https://prove2.me/theorems/345b34bf-497b-4ea0-a25a-d46e8b71fe71
-- title:
--   Actual BV source Lévy residual induces a Stieltjes measure with exact increment masses
-- statement:
--   For the original spectrally negative Lévy process X in the bounded-variation regime, a P-a.s. event supports a positive Stieltjes measure built from the genuine path's monotone residual R_t=d t-X_t. On each half-open interval (s,t] its mass is the nonnegative residual increment (d t-X_t)-(d s-X_s), expressed through ENNReal.ofReal. Uses original sample ω, not any equal-law replacement. This is pathwise drift-minus-X measure representation; no claim of Poisson jump count, atom-only representation, or predictable compensation.
-- source:
--   Pinned original structure 933ced80-71c1-4c0f-a6a7-ab7757fc97e9, canonical Proved a.e. monotone source residual f6cc1059-e8ca-403e-8d73-71a139d3dc4c, pinned Mathlib Monotone.stieltjesFunction, Monotone.stieltjesFunction_eq, ContinuousWithinAt.rightLim_eq, StieltjesFunction.measure_Ioc. Audited as a distinct actual-X BV Stieltjes measure interface, not a Poisson compensator.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_residual_stieltjes_interval_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      ∀ s t : ℝ≥0,
        F.measure (Ioc s t) =
          ENNReal.ofReal (((t : ℝ) * X.drift - X.X t ω) -
            ((s : ℝ) * X.drift - X.X s ω)) := by sorry
