-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
-- name    : AvramDividend.Classical.unbounded_unstopped_scale_martingale_forces_nonpositive_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:17:54.372605+00:00
-- url     : https://prove2.me/theorems/64e6340f-9b5e-4f1c-8452-c6d8efe86651
-- title:
--   Un-stopped scale martingale at zero forces nonpositive Lévy paths
-- statement:
--   For unbounded variation with W(0)=0, if the un-killed discounted q-scale reward e^{-qt}W(X_t) were a genuine nonnegative martingale started from X_0=0, then every fixed-time increment would be nonpositive almost surely. This is deduced by the pinned result that nonnegative zero-start martingales vanish and strict positivity of the q-scale on (0,infinity). It explicitly shows the obstruction to the un-stopped martingale hypothesis currently used by the Avram strict two-sided exit route; the source-faithful process is stopped at lower ruin.
-- source:
--   Proved nonnegative_zero_initial_martingale_vanishes_ae, scaleFunction_strict_pos_of_unbounded_variation, and IsScaleFunction nonnegativity.

import Theorems.Thm_AvramDividend_Classical_nonnegative_zero_initial_martingale_vanishes_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.unbounded_unstopped_scale_martingale_forces_nonpositive_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0)
    (hStart : ∀ᵐ ω ∂P, X.X 0 ω = 0)
    (hMart : Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by sorry
