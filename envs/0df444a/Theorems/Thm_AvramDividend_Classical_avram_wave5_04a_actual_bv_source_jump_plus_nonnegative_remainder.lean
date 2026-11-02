-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_jump_plus_nonnegative_remainder
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_jump_plus_nonnegative_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:34:11.117057+00:00
-- url     : https://prove2.me/theorems/775a6a71-8b9b-4c7b-a57e-11669cbba114
-- title:
--   Actual original BV Levy source residual equals its stopped jump magnitude plus a nonnegative remainder
-- statement:
--   For one P-almost-sure event of the actual bounded-variation SpectrallyNegativeLevy source, there exists its intrinsic Stieltjes residual F(t)=t*X.drift-X_t. On every interval (s,t], including any samplewise stopped interval, the complete actual negative-source-jump magnitude series plus a nonnegative extended-real remainder equals F.measure((s,t]). The remainder allows diffuse downward finite variation; no assumption that it vanishes, pure-jump equality, or independent Poisson model is made. This is the exact nonnegative residual budget needed for finite-partition C1 source-chain inequalities.
-- source:
--   Avram Wave 5 Chat 04-A, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Source exact accepted 6db7ca71-b2a6-468c-9020-c8178e8d9dd3 all-time-set original Stieltjes jump atom domination, with tsub_add_cancel_of_le in pinned Mathlib. The remainder is a positive interval mass budget, not a claim that the residual is atom-free or a separate measure.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_jump_plus_nonnegative_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        ∃ r : ℝ≥0∞,
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ∈ Ioc s t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0) + r = F.measure (Ioc s t) := by sorry
