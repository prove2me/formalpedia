-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_centered_count_past_event_l1_zero
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_centered_count_past_event_l1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:55:44.501997+00:00
-- url     : https://prove2.me/theorems/131a6bb4-b014-4b29-86ca-30fd33367c82
-- title:
--   Finite-rate original intrinsic compensated marked count is L1 and has zero past-event integral
-- statement:
--   For the original Lévy process and a Borel jump-mark set of finite Lévy intensity, assuming the exact original intrinsic unconditional count rate, the compensated real increment has finite L1 norm and zero integral against every event in the actual past filtration F_s. This is the signed martingale-difference event test needed for predictable compensation, with the genuine original intrinsic jump measure and (s,t] conventions.
-- source:
--   Original source finite-nu count real integrability and past real mean accepted proofs; pinned Mathlib setIntegral_const and integral_sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_nu_past_real_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_centered_count_past_event_l1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
    ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫ ω in A, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by sorry
