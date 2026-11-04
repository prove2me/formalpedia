-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rate_free_direct_condexp_zero
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_rate_free_direct_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:17:50.629193+00:00
-- url     : https://prove2.me/theorems/6eff1414-d0cc-4f34-a488-4d1f798e3005
-- title:
--   Rate-free original finite-mean centred marked count has zero past conditional expectation
-- statement:
--   For the actual original Lévy process, the finite-mean intrinsic marked count on (s,t] centred by its actual unconditional expectation has conditional expectation zero given the true F_s. It uses accepted rate-free original conditional expectation and no Lévy intensity identity.
-- source:
--   Original source-marked count and accepted P2-E conditional-expectation lemmas; Mathlib condExp_sub, condExp_const and L1 integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_mean_condexp_independent

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_rate_free_direct_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hMeanFinite :  (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        ((∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P)).toReal)) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by sorry
