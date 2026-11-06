-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_interior_finite_tag_C1_prejump_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_interior_finite_tag_C1_prejump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:02:37.070851+00:00
-- url     : https://prove2.me/theorems/1b263528-0f6c-42ca-b2df-9974df1e85a4
-- title:
--   Strict interior original Lévy finite-tag nonlinear source convergence from C1 regularity
-- statement:
--   For finitely tagged genuine original spectrally negative Lévy jumps with their pre-event and post-jump reserves inside an open C1 generator domain, the original nonlinear jump sum at physical tagged reserve approximants converges to the predictable pre-event source sum. The only dynamic premise is convergence of genuine physical tagged states at those source times.
-- source:
--   Direct source-faithful strict-interior completion of the finite-tag Lévy nonlinear source bridge, using original C1 generator regularity and the finite-tag pre-jump convergence theorem. The cap/ruin boundary remains a separate stopped localisation task.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_interior_finite_tag_C1_prejump_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
    (T : Finset ℝ≥0) (z : ℕ → ℝ≥0 → ℝ)
    (u discount : ℝ≥0 → ℝ)
    (hz : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hinside : ∀ t ∈ T,
      u t ∈ U ∧
      u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ U) :
    Tendsto
      (fun k => T.sum (fun t =>
        discount t *
          (w (z k t +
            (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) -
           w (z k t)))) atTop
      (nhds (T.sum (fun t =>
        discount t *
          (w (u t +
            (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) -
           w (u t))))) := by sorry
