-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_BV_physical_lefttag_stopped_infinite_jump_limit
-- name    : AvramDividend.Classical.avram_p3_2_original_BV_physical_lefttag_stopped_infinite_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:21:28.148073+00:00
-- url     : https://prove2.me/theorems/3ac38d0a-4157-417c-9f60-6895147b1884
-- title:
--   True bounded-variation controlled physical left-tags converge to the original stopped infinite nonlinear Lévy source
-- statement:
--   Almost surely for the original bounded-variation spectrally negative Lévy X and original dividend strategy D, a common actual left-tag physical mesh approaching every finite-horizon true jump, a compact strict-interior stopped reserve band and bounded discount imply convergence of the full infinite-activity nonlinear jump sum from physical tagged reserves to the original predictable pre-event source. The real original BV jump variation supplies domination.
-- source:
--   Integrates original leftlimit theorem 015a831f with new source-exact original finite-stop BV dominated convergence and actual C1 compact jump increment domination. Remaining boundary localisation, full grid-cell aggregation and drift/discount compensation are still separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_BV_physical_lefttag_stopped_infinite_jump_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (S : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (w : ℝ → ℝ) (U : Set ℝ)
      (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
      (lo hi : ℝ) (hSub : Set.Icc lo hi ⊆ U)
      (lefttag : ℕ → ℝ≥0 → ℝ≥0)
      (discount : ℝ≥0 → ℝ) (M : ℝ),
      0 ≤ M →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 →
        Tendsto (fun k => lefttag k t) atTop (𝓝[<] t)) →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 →
        (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) ∈ U ∧
        (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ∈ U) →
      (∀ᶠ k in atTop, ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 →
        (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) ∈ Set.Icc lo hi ∧
        ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω)) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ∈ Set.Icc lo hi) →
      (∀ t : ℝ≥0, |discount t| ≤ M) →
      Tendsto
        (fun k => ∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 then
            discount t *
              (w ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t)) - w (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω))
          else 0) atTop
        (nhds (∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 then
            discount t *
              (w ((Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t)) - w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t))
          else 0)) := by sorry
