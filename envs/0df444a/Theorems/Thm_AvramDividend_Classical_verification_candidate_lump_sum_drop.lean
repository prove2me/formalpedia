-- Prove2me | Theorems.Thm_AvramDividend_Classical_verification_candidate_lump_sum_drop
-- name    : AvramDividend.Classical.verification_candidate_lump_sum_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:23:30.031987+00:00
-- url     : https://prove2.me/theorems/f1df0ea2-675f-489a-a2f1-d810e81bb0dd
-- title:
--   Derivative floor controls the value drop from an admissible lump-sum dividend
-- statement:
--   If the verification candidate has marginal value at least one throughout the reserve interval traversed by a nonnegative lump-sum dividend δ, then paying that dividend lowers w by at least δ: w(u)-w(u-δ)≥δ. This is the deterministic finite-variation jump estimate used in the proof of Proposition 4(i).
-- source:
--   Direct mean-value consequence of the gradient inequality 1-w'≤0 from Eq. (5.8) in Avram–Palmowski–Pistorius, used for lump-sum dividend jumps in the local verification theorem.

import Mathlib

open Set

theorem AvramDividend.Classical.verification_candidate_lump_sum_drop
    (w : ℝ → ℝ) (u δ : ℝ) (hδ : 0 ≤ δ)
    (hcont : ContinuousOn w (Icc (u - δ) u))
    (hdiff : DifferentiableOn ℝ w (Ioo (u - δ) u))
    (hderiv : ∀ y ∈ Ioo (u - δ) u, 1 ≤ deriv w y) :
    δ ≤ w u - w (u - δ) := by sorry
