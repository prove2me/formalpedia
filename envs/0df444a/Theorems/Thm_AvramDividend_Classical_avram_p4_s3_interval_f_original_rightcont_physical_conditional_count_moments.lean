-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
-- name    : AvramDividend.Classical.avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:23:21.7009+00:00
-- url     : https://prove2.me/theorems/4208c6b2-33ae-44e0-a564-284bc8addd77
-- title:
--   Original physical marked future-count conditional L2 moments under the same right-continuous filtration
-- statement:
--   For the exact original Lévy process X on its original probability space, the physical marked count of X on (s,t] has conditional mean zero and conditional centred square r under the right-continuous filtration. This follows from the proved same-path right-continuous Lévy lift and the proved original physical conditional-moment theorem. Its genuine unconditional first/square integrability and moments remain explicit; no law replacement, extra sample space or Poisson surrogate is introduced.
-- source:
--   Proved e58a099d-9977-4265-9e76-7a5f0f6aa758 right-continuous Lévy lift Y with Y.X=X.X and Y.ν=X.ν, and newly accepted/public d42bd524-886f-4db6-973a-2b87823615fe same-X physical count conditional moments. Pointwise path equality transports N without changes.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_physical_conditional_count_moments
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (N : Ω → ℝ≥0∞)
    (hN : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hInt : Integrable (fun ω => (N ω).toReal - r) P)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hMean : (∫ ω, (N ω).toReal - r ∂P) = 0)
    (hVariance : (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r) :
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P] (fun _ => r)) := by sorry
