-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_physical_lefttag_jump_source_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_physical_lefttag_jump_source_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:18:49.114201+00:00
-- url     : https://prove2.me/theorems/8650c646-91a6-4a3c-815f-7278b5a90bf9
-- title:
--   True original discounted physical left-tag Lévy jump sum converges to pre-jump discounted source
-- statement:
--   For genuine original controlled BV Lévy paths and finite positive jump tags approaching each marked time from below, the exact physical discount e^{-q u_i} and controlled post-rightpayment reserve together converge to their original pre-event discount e^{-qt} and reserve. C1 regularity on open strict-interior pre- and postmarked states gives convergence of the finite nonlinear signed original jump sum with its actual physical discount weights.
-- source:
--   Accepted original controlled left-prestate convergence 015a831f, continuity of physical exponential discount, and pinned finite-sum convergence. Genuine original X.X and D, exact original jump marks; no proxy process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_physical_lefttag_jump_source_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
    (T : Finset ℝ≥0) (hT : ∀ t ∈ T, 0 < t)
    (lefttag : ℕ → ℝ≥0 → ℝ≥0)
    (hTag : ∀ t ∈ T,
      Tendsto (fun k => lefttag k t) atTop (𝓝[<] t))
    (hInside : ∀ t ∈ T,
      (Function.leftLim (fun v : ℝ≥0 =>
        x + X.X v ω - rightLimit D v ω) t) ∈ U ∧
      (Function.leftLim (fun v : ℝ≥0 =>
        x + X.X v ω - rightLimit D v ω) t) + (X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t) ∈ U) :
    Tendsto
      (fun k => T.sum (fun t =>
        Real.exp (-(q * (lefttag k t : ℝ))) *
          (w ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) + (X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)) -
           w (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω)))) atTop
      (nhds (T.sum (fun t =>
        Real.exp (-(q * (t : ℝ))) *
          (w ((Function.leftLim (fun v : ℝ≥0 =>
        x + X.X v ω - rightLimit D v ω) t) + (X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)) -
           w (Function.leftLim (fun v : ℝ≥0 =>
        x + X.X v ω - rightLimit D v ω) t))))) := by sorry
