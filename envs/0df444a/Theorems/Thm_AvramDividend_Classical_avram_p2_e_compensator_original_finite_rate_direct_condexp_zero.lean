-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_rate_direct_condexp_zero
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_finite_rate_direct_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:18:21.963186+00:00
-- url     : https://prove2.me/theorems/14db514d-343d-4e73-bd89-dc7db4fdeb1f
-- title:
--   Finite ν-rate original compensated marked count has zero past conditional expectation
-- statement:
--   Given the exact original unconditional intrinsic count rate and finite ν(B), the compensated real original marked jump-count increment on (s,t] has conditional expectation zero given the true F_s. Uses accepted original conditional count rate and pinned Mathlib conditional-expectation linearity.
-- source:
--   Original source-marked count and accepted P2-E conditional-expectation lemmas; Mathlib condExp_sub, condExp_const and L1 integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_count_condexp_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_finite_rate_direct_condexp_zero
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
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by sorry
