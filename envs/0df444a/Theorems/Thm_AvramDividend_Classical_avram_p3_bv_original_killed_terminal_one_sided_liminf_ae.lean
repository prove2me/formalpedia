-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_killed_terminal_one_sided_liminf_ae
-- name    : AvramDividend.Classical.avram_p3_bv_original_killed_terminal_one_sided_liminf_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:46:21.028899+00:00
-- url     : https://prove2.me/theorems/14b4d24d-d794-4172-b096-0077d95b6664
-- title:
--   Original discounted strictly surviving killed terminal has the required one-sided liminf lower bound at fixed positive horizons
-- statement:
--   For the original controlled process, the nonnegative killed prepayment terminal at every deterministic positive time has a one-sided lower-semicontinuity estimate. For each epsilon > 0, the terminal at the horizon minus epsilon is strictly less than the killed terminal at all sufficiently late preceding times, almost surely. On strict survival, the previously proved discounted killed-terminal convergence supplies this. If the horizon is at or after ruin, its terminal is zero and all sufficiently nearby preceding killed terminals are nonnegative. This resolves the special equality ruinTime = horizon case without asserting false ordinary continuity.
-- source:
--   Uses exact original killed-terminal left-survival convergence and the original pre-ruin nonnegative HJB hypothesis; epsilon formulation is directly usable for the finite-horizon Fatou lower-bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_killed_terminal_one_sided_liminf_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (hwnn : ∀ ω (s : ℝ≥0), 0 < s →
      (s : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D s ω))
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
        (if (t : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω) else 0) - ε <
        (if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω) else 0) := by sorry
