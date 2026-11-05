-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_killed_terminal_left_grid_lower_bound_ae
-- name    : AvramDividend.Classical.avram_p3_bv_original_killed_terminal_left_grid_lower_bound_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:58:12.26649+00:00
-- url     : https://prove2.me/theorems/3aab1a39-b2fd-417b-8896-8e1622921d6c
-- title:
--   Original killed HJB terminal lower bound along every grid approaching the horizon strictly from the left
-- statement:
--   For the actual original controlled Lévy process, every sequence of nonnegative grid times converging to a strictly positive horizon from its left-neighbourhood filter satisfies the one-sided epsilon lower bound on the original killed pre-rightpayment discounted terminal almost surely. At the precise ruin horizon the killed payoff may jump down, but the inequality remains valid. This prepares the finite-grid Fatou passage without a replacement process or compensation premise.
-- source:
--   Filter.Tendsto.eventually pullback of the source-exact original killed terminal one-sided liminf lemma, with exactly the original strict survival predicate and riskProcess.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_killed_terminal_one_sided_liminf_ae
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_killed_terminal_left_grid_lower_bound_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (hwnn : ∀ ω (s : ℝ≥0), 0 < s →
      (s : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D s ω))
    (t : ℝ≥0) (ht : 0 < t) (u : ℕ → ℝ≥0)
    (hu : Tendsto u atTop (𝓝[<] t)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (if (t : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω) else 0) - ε <
        (if (u n : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (u n : ℝ))) * w (riskProcess X x D (u n) ω) else 0) := by sorry
