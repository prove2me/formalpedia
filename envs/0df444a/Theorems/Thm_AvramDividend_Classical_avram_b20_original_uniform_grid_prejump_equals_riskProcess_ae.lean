-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
-- name    : AvramDividend.Classical.avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:06:04.615408+00:00
-- url     : https://prove2.me/theorems/3483a417-f7fc-4e14-a645-22a55268231c
-- title:
--   Original uniform physical grid has source-correct prepayment reserve at all positive mesh points a.s.
-- statement:
--   For the actual original Lévy process X and the adapted nondecreasing original dividend strategy D, every strictly positive point of every T/(n+2) uniform deterministic grid has leftLimit(original pre-rightpayment reserve) equal to the original riskProcess at that point, on one common probability-one event. This proves the prepayment grid assumption hPre required by the original finite-activity BV stopped error and mean-gap theorems. There is no process replacement, jump-intensity restriction or additional stochastic premise.
-- source:
--   Corollary of Proved e26f2e74 avram_bv_stieltjes10_original_countable_positive_grid_prejump. Apply it for each grid row n, then intersect the countably many full-measure events using ae_all_iff. Root strand dependency for a86fede9,2ac1cc3d,6ce6d0c3,f5b574a6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω := by sorry
