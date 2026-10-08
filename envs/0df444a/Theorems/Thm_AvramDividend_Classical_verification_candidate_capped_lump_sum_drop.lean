-- Prove2me | Theorems.Thm_AvramDividend_Classical_verification_candidate_capped_lump_sum_drop
-- name    : AvramDividend.Classical.verification_candidate_capped_lump_sum_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:52:44.213472+00:00
-- url     : https://prove2.me/theorems/f373fa8b-4cb4-4eac-9b58-871a70c5d3bf
-- title:
--   Capped verification candidate absorbs every feasible dividend lump
-- statement:
--   If a verification candidate is continuous on nonnegative reserves, differentiable inside the capped positive domain, and has derivative at least one there, then any feasible lump dividend δ that leaves nonnegative reserves and starts from a reserve u with ofReal u≤C decreases w by at least δ. This is the exact deterministic jump estimate needed in the finite-horizon verification argument, including the boundary u=C.
-- source:
--   Deterministic consequence of the marginal-dividend inequality in Eq. (5.8), used in the jump term of Proposition 4(i), Avram–Palmowski–Pistorius (2007). Reduces to verification_candidate_lump_sum_drop by restricting the global capped hypotheses to [u-δ,u].

import Mathlib
import Theorems.Thm_AvramDividend_Classical_verification_candidate_lump_sum_drop

open Set
open scoped ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.verification_candidate_capped_lump_sum_drop
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_diff : DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u δ : ℝ) (hδ : 0 ≤ δ) (hpost : 0 ≤ u - δ)
    (hcap : ENNReal.ofReal u ≤ C) :
    δ ≤ w u - w (u - δ) := by sorry
