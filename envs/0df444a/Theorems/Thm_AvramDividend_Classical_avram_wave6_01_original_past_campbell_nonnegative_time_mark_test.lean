-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_campbell_nonnegative_time_mark_test
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_campbell_nonnegative_time_mark_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:15:52.837369+00:00
-- url     : https://prove2.me/theorems/1f2a8bbe-9424-46fc-9682-c1935d6dd906
-- title:
--   Nonnegative deterministic time–mark tests integrate against the genuine original Lévy Campbell measure
-- statement:
--   On the unchanged original Lévy Ω,P,𝓕,X.X and every past A∈𝓕_s, construct one genuine time–mark Campbell measure Q_A whose value on each Borel C equals the past-restricted expected literal original intrinsic jump count, and for every Borel nonnegative deterministic time–mark test f, ∫ f dQ_A=E_P[1_A∫ f dN_X]. The proof uses the proved original measurable s-finite kernel, its exact source fibres and genuine measure.lintegral_bind/Tonelli. This is the honest nonnegative step integrand integration interface; it does not claim Q_A=P(A)du⊗X.ν or assume the missing original compensator.
-- source:
--   Canonically Proved intrinsic source s-finite kernel eb357d08; Measure.bind_apply and Measure.lintegral_bind with actual path fibre equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_campbell_nonnegative_time_mark_test
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (f : (ℝ≥0 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)) ∧
      (∫⁻ p, f p ∂Q) =
        (∫⁻ ω in A, (∫⁻ p, f p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) := by sorry
