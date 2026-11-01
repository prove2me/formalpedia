-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_pathwise_record_height_potential_eq_inverse_hazard
-- name    : AvramDividend.Classical.avram_wave4_01_original_pathwise_record_height_potential_eq_inverse_hazard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:02:59.031994+00:00
-- url     : https://prove2.me/theorems/395148cb-c2ba-46ee-a06e-381cedc6f43a
-- title:
--   The expected genuine pathwise killed first-record height occupation potential is the reciprocal q-scale logarithmic derivative
-- statement:
--   For the genuine original Lévy process in the pure infinite-small-negative-jump branch, the expectation of the actual pathwise integral over positive record heights of exp(-q T_h) killed on the event T_h<D_a equals the reciprocal first-record hazard W(a)/W'(a). The proof first uses the new joint measurability of the exact original reward and the genuine Tonelli swap, then applies the established real spatial q-scale potential identity. The inner killed expectation is bounded by one under the actual probability law, so the integrand is finite everywhere; pinned integral_toReal bridges the real and extended nonnegative spatial integrals. No Standing, Esscher-excursion surrogate or unproved stochastic axiom.
-- source:
--   Requires newly authored canonical Proved joint reward measurability and source-law Tonelli swap, plus already Proved original discount le_one UUID 7a08c9f8-d2f2-4c32-a54f-429d24f82029 and real spatial inverse hazard potential UUID 1bc8ca04-1571-40a3-998e-8ddd8b9b9d8f. Pinned Mathlib MeasureTheory.integral_toReal and Measurable.lintegral_prod_right exact types confirmed; X.isProbability supplies SFinite P. Dependencies must be Proved before publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_height_tonelli_swap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_pathwise_record_height_potential_eq_inverse_hazard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ ω, ∫⁻ h in Ioi (0 : ℝ),
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ∂volume ∂P).toReal =
    (deriv W a / W a)⁻¹ := by sorry
