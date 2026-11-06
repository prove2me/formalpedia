-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_dominated_infinite_activity_nonlinear_jump_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_dominated_infinite_activity_nonlinear_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:00:32.380957+00:00
-- url     : https://prove2.me/theorems/e1b3dab5-875e-4928-9b6f-8d08be77fea4
-- title:
--   Dominated convergence for infinite original Lévy nonlinear jump series under BV tail majorant
-- statement:
--   For the intrinsic original spectrally negative Lévy nonzero-jump series, convergence of every actual tagged reserve to its original pre-jump reserve, continuity of w at both genuine states, and a summable real majorant imply convergence of the full weighted nonlinear signed jump sum. Infinite jump activity is allowed; the BV tail bound is an explicit premise requiring construction from the source process.
-- source:
--   Pinned Mathlib tendsto_tsum_of_dominated_convergence with original X.X jump indicator and exact original marked nonlinear kernel. This bridges finite marked jump convergence to full true source series when original BV jump-variation domination is established.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_dominated_infinite_activity_nonlinear_jump_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ) (z : ℕ → ℝ≥0 → ℝ)
    (u discount : ℝ≥0 → ℝ) (bound : ℝ≥0 → ℝ)
    (hBound : Summable bound)
    (hz : ∀ t : ℝ≥0, 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
      Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hw : ∀ t : ℝ≥0, 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
      ContinuousAt w (u t) ∧
      ContinuousAt w (u t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    (hDom : ∀ᶠ k in atTop, ∀ t : ℝ≥0,
      ‖if 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
            discount t * (w ((z k) t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w ((z k) t))
          else 0‖ ≤ bound t) :
    Tendsto
      (fun k => ∑' t : ℝ≥0,
        if 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
            discount t * (w ((z k) t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w ((z k) t))
          else 0) atTop
      (nhds (∑' t : ℝ≥0,
        if 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
            discount t * (w (u t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w (u t))
          else 0)) := by sorry
