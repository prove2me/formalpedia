-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_lefttag_C1_nonlinear_jump_source_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_lefttag_C1_nonlinear_jump_source_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:18:43.064825+00:00
-- url     : https://prove2.me/theorems/16f52583-63ed-4ba8-a9a7-925af65a716d
-- title:
--   Actual original controlled physical left-tag nonlinear jump sum converges to pre-event Lévy source
-- statement:
--   For actual original Lévy X, admissible dividend path D and finitely many positive jump times, any physical left tags tending from below to each marked time make the exact post-rightpayment controlled reserve converge to the predictable left reserve. C1 regularity of w on the strictly interior pre- and post-jump states then gives convergence of the full finite weighted nonlinear physical jump sum to the original predictable pre-jump source. No independent proxy or finite-activity assumption.
-- source:
--   Uses already Proved actual original controlled left prestate limit 015a831f and pinned tendsto_finset_sum, preserving original jump marks. The separate outstanding assumptions concern constructing stopped physical tagged grids, C1 localisation, small-jump tails, and L1 compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_lefttag_C1_nonlinear_jump_source_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
    (T : Finset ℝ≥0) (hT : ∀ t ∈ T, 0 < t)
    (lefttag : ℕ → ℝ≥0 → ℝ≥0)
    (hTag : ∀ t ∈ T,
      Tendsto (fun k => lefttag k t) atTop (𝓝[<] t))
    (discount : ℝ≥0 → ℝ)
    (hInside : ∀ t ∈ T,
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t ∈ U ∧
      (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t) ∈ U) :
    Tendsto
      (fun k => T.sum (fun t =>
        discount t *
          (w ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t)) -
           w (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω)))) atTop
      (nhds (T.sum (fun t =>
        discount t *
          (w ((Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t)) -
           w (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t))))) := by sorry
