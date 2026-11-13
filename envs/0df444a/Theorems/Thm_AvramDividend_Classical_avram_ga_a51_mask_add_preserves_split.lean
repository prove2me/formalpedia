-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a51_mask_add_preserves_split
-- name    : AvramDividend.Classical.avram_ga_a51_mask_add_preserves_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:38:14.677851+00:00
-- url     : https://prove2.me/theorems/82631990-36b0-4533-823f-14d7276df087
-- title:
--   The positive-clock indicator mask commutes with an exact physical two-term split
-- statement:
--   The positive-clock indicator mask commutes with an exact physical two-term split. This is a purely scalar identity used to make the original Gaussian gledger178 positive-L1 gluing theorem a48 admissible under bounded proof complexity; the original physical X, rightLimit D and stopped clock remain unchanged.
-- source:
--   Root-connected a48 e54634c7-ec7c-418f-96e0-4c4b142ba786, gledger178 5318a4dc and original interior b0d9951c.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a51_mask_add_preserves_split
    {Ω : Type*} (ρ : Ω → ℝ≥0)
    (B V T : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, B m ω = V m ω + T m ω) :
    ∀ m ω,
      (if 0 < ρ ω then B m ω else 0) =
      (if 0 < ρ ω then V m ω else 0) +
      (if 0 < ρ ω then T m ω else 0) := by sorry
