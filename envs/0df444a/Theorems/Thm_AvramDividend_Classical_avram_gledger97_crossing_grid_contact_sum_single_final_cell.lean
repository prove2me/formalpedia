-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger97_crossing_grid_contact_sum_single_final_cell
-- name    : AvramDividend.Classical.avram_gledger97_crossing_grid_contact_sum_single_final_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:09:34.962814+00:00
-- url     : https://prove2.me/theorems/abbbc11b-7d47-41e0-ac96-8c0cb8f99295
-- title:
--   After the first stopping-grid crossing only one terminal dividend-contact cell survives
-- statement:
--   A clipped deterministic grid is constant after its first stopping-time crossing. Consequently every dividend-contact cell beyond the crossing is exactly zero, so the original finite contact sum consists only of strict interior cells plus one final crossing cell. This is a pure finite-sum identity and leaves the genuine original Stieltjes estimate to other lemmas.
-- source:
--   Original gledger81 contact-sum bookkeeping: after-stop cells are zero and exactly one final crossing term remains, preventing duplicate terminal payment accounting.

import Mathlib
namespace AvramDividend
namespace Classical
end Classical
end AvramDividend
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger97_crossing_grid_contact_sum_single_final_cell
    (w : ℝ → ℝ) (E : ℝ≥0 → ℝ) (v : ℕ → ℝ≥0)
    (Y Z : ℕ → ℝ) (k N : ℕ) (hkN : k < N)
    (hpost : ∀ i : ℕ, k < i → Y (i + 1) = Z i) :
    (∑ i ∈ Finset.range N, E (v (i + 1)) * (w (Y (i + 1)) - w (Z i))) =
      (∑ i ∈ Finset.range k, E (v (i + 1)) * (w (Y (i + 1)) - w (Z i))) +
        E (v (k + 1)) * (w (Y (k + 1)) - w (Z k)) := by sorry
