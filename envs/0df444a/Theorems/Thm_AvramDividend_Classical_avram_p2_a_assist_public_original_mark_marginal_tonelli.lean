-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_public_original_mark_marginal_tonelli
-- name    : AvramDividend.Classical.avram_p2_a_assist_public_original_mark_marginal_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:47:50.472196+00:00
-- url     : https://prove2.me/theorems/4b113001-a6ed-47bd-8a27-c923b4b8476c
-- title:
--   Public original source mark marginal Tonelli bridge
-- statement:
--   For the actual original spectrally negative Lévy jump-count kernel, construct the genuine time-T expected mark measure rho and prove that integrating any nonnegative measurable mark function against rho equals the expected intrinsic mark-sum integral over (0,T].
-- source:
--   Public Proved original intrinsic time-mark weighted Fubini UUID 979be838-13c7-414d-8b1b-bce72fd2022b and pinned Mathlib measure map, restriction and indicator identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_assist_public_original_mark_marginal_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ ρ : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∫⁻ y, g y ∂ρ) =
        (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
          g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by sorry
