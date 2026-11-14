-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB309_translated_inverse_sqrt_open_cell_lintegral_bound
-- name    : AvramDividend.Classical.avram_gbB309_translated_inverse_sqrt_open_cell_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:03:25.202271+00:00
-- url     : https://prove2.me/theorems/d738b529-eaea-47aa-9606-e32dfa50aac3
-- title:
--   Translated inverse-square-root singular real-time cell lintegral is bounded by twice the square-root width
-- statement:
--   For a nonnegative real cell width and an integrable translated inverse-square-root singular time kernel on its right-closed interval, the extended-nonnegative-real lintegral over the strictly open cell is bounded by twice the square root of the width. Use the Proved B280 translated Gaussian real integral identity, the B303 real-to-lintegral conversion, and set-restriction monotonicity. This is the singular-time integral component of the original B308 Gaussian fibre bound.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB309_translated_inverse_sqrt_open_cell_lintegral_bound
    (s δ : ℝ) (hδ : 0 ≤ δ)
    (hf : IntegrableOn
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
      (Set.Ioc s (s + δ)) volume) :
    (∫⁻ t in Set.Ioo s (s + δ),
      ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume) ≤
      ENNReal.ofReal (2 * Real.sqrt δ) := by sorry
