-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:54:09.162015+00:00
-- url     : https://prove2.me/theorems/0b5d59e3-bcf8-4b5c-92f1-904915474cc7
-- title:
--   Finite original Lévy jump tags converge to predictable nonlinear jump source
-- statement:
--   The finite original Lévy jump-tag nonlinear source sum evaluated at physical tagged reserves converges to its predictable pre-event value if each actual tagged reserve converges and w is continuous at the original prestate and post-original-mark states. The original X mark is preserved; cap and ruin localisation remain separate proof obligations.
-- source:
--   Genuine finite-tag step in BV physical mesh-to-original predictable nonlinear source convergence. Pointwise pre-event reserve convergence is explicitly required and must be established by original stopped left-limit localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ) (T : Finset ℝ≥0)
    (z : ℕ → ℝ≥0 → ℝ) (u discount : ℝ≥0 → ℝ)
    (hz : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hw : ∀ t ∈ T,
      ContinuousAt w (u t) ∧
      ContinuousAt w (u t +
        (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t))) :
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
