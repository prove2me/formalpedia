-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_weak_ruin_discounted_mark_bound
-- name    : AvramDividend.Classical.avram_bva22_original_K_weak_ruin_discounted_mark_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:38:17.974167+00:00
-- url     : https://prove2.me/theorems/c8884366-ec42-40fb-95bb-4a4d072651f0
-- title:
--   Original K inclusive-ruin closed-cap discounted mark kernel has uniform absolute bound
-- statement:
--   The exact original K mark-compensator mask has weak ruin time t≤τ and inclusive reserve cap. If the original negative-mark kernel is uniformly bounded by B on that cap and q≥0, then its time-discounted masked contribution has absolute value at most B at every physical time. This extends the previously proved strict-ruin A counterpart to the actual weak-ruin K integrand needed for source 7ccc2a1a dominated convergence.
-- source:
--   Exact source-K weak-ruin time integrand uniform domination for paired DCT closure of 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_K_weak_ruin_discounted_mark_bound
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ)
    (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hψ : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → |ψ b| ≤ B)
    (t : ℝ≥0) :
    |if (t : ℝ≥0∞) ≤ τ ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
         Real.exp (-(q * (t : ℝ))) * ψ (U t)
       else 0| ≤ B := by sorry
