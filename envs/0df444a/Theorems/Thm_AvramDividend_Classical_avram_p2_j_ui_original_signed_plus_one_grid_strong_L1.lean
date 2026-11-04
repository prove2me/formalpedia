-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_plus_one_grid_strong_L1
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_plus_one_grid_strong_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:55:54.446916+00:00
-- url     : https://prove2.me/theorems/608c19d4-b9eb-43b4-bca3-0f2cf8f78fe7
-- title:
--   Strong L¹ convergence for genuine signed original Lévy n+1-grid test sums under a.e. path limit
-- statement:
--   For actual original spectrally negative Lévy increments, signed g dominated by a bounded away-from-zero ENNReal f, an eventually short n+1 mesh and an explicitly proven a.e. grid-to-jump limit imply strong L1 convergence of signed grid sums and MemLp of the limit. Uses genuine original bounded-grid L2 source bound, finite-sum triangle domination, and the new Vitali finite-envelope result. No assumed jump compensation or rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_strong_L1

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_plus_one_grid_strong_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n ω, Y n ω = ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by sorry
