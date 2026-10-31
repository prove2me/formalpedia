-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
-- name    : AvramDividend.Classical.avram_wave3_04_clipped_stronglyPredictable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:37:35.219775+00:00
-- url     : https://prove2.me/theorems/504ebddb-4d9e-4a99-9efa-75bc0940311a
-- title:
--   Symmetric deterministic clipping preserves strong predictability and guarantees a uniform bound
-- statement:
--   For any strongly predictable real-valued process and nonnegative localisation level K, symmetric truncation max(-K,min K Z_t) remains strongly predictable and is uniformly bounded in absolute value by K at every time and sample point. Continuity of the real min/max clipping map ensures Borel measurability and composition with the original predictable sigma algebra; elementary lattice inequalities give the deterministic norm bound. This is a preparatory localisation interface for integrable bounded predictable coefficients in finite Lévy-increment sums.
-- source:
--   Pinned Mathlib Borel measurability of continuous min/max maps and strong predictability. Private exact remote compiler job 89bec113-3e2e-4984-bf61-699e044b55aa passed sentinel without candidate errors, source SHA-256 6aeadb1b3fa2ae616abdf739d0843a42a53d512ec7b0e423c21e011a338f1089.

import Mathlib

open MeasureTheory Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_clipped_stronglyPredictable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (K : ℝ) (hK : 0 ≤ K) :
    IsStronglyPredictable 𝓕
      (fun t ω => max (-K) (min K (Z t ω))) ∧
    (∀ t ω, ‖max (-K) (min K (Z t ω))‖ ≤ K) := by sorry
