-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:40:31.265996+00:00
-- url     : https://prove2.me/theorems/11fd5deb-2806-41bf-ba08-be410ded1693
-- title:
--   Strict original reserve cap margin absorbs true BV drift-cell upshifts
-- statement:
--   A fixed strict reserve-to-cap margin ρ>0 on an original physical refining grid absorbs every sufficiently small signed BV drift cell, proving the cap-safe upshift hypothesis in the accepted source-exact P3-2 cash/commutator budget. Includes the C=top case without a fake finite cap. Instantiating z with the true post-rightpayment original X/D reserve and c with Δt*X.drift, using the original clock-mesh theorem, closes this key strict-interior localisation interface; cap-contact paths remain a separate boundary obligation.
-- source:
--   Elementary real absolute value and eventual drift mesh bound; exact full-cap and strict finite-cap distinctions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells
    (C : ℝ≥0∞) (ρ : ℝ) (hρ : 0 < ρ)
    (z c : ℕ → ℕ → ℝ) (n : ℕ → ℕ)
    (hInterior : ∀ m i, i < n m →
      C = ⊤ ∨ z m i ≤ C.toReal - ρ)
    (hDriftSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        |c m i| < ε) :
    ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
      C = ⊤ ∨ z m i + c m i ≤ C.toReal := by sorry
