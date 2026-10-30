-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_clipped_ceiling_grid_killed_integrable
-- name    : AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:04:28.809132+00:00
-- url     : https://prove2.me/theorems/1a9e5cb6-4916-4f4a-acc4-d397e4a5f4e6
-- title:
--   Genuine BV clipped first-exit history-killed q-scale reward is integrable at all grid meshes
-- statement:
--   For every original-Lévy two-sided grid first-exit index and its horizon-clipped clock, the true discounted q-scale payoff killed on any negative past reserve is Bochner integrable. The source grid can be identified with the bounded monotone clipped clock by the accepted real hittingBtwn congruence, allowing the genuine BV integrability theorem to apply.
-- source:
--   Accepted source BV killed bounded-grid integrability, clipped monotone clock and actual ceiling first-hitting clock congruence; no independent random-history measurability assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_bounded_grid_reward_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_integrable
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hx : 0 ≤ x) (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
    (K : Ω → ℕ)
    (hK : ∀ η, K η = hittingBtwn
      (fun (k : ℕ) ξ => max (X.X ((k : ℝ≥0) * δ) ξ - (a-x))
        ((-x) - X.X ((k : ℝ≥0) * δ) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η) :
    Integrable (fun ω =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K η : ℝ≥0) * δ) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min ((K η : ℝ≥0) * δ) T) : ℝ))) *
          W (x + X.X (min ((K η : ℝ≥0) * δ) T) η)) ω) P := by sorry
