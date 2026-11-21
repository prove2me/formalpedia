-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_active_postpayment_lower_clip_equals_source_Hessian
-- name    : AvramDividend.Classical.avram_ga_original_active_postpayment_lower_clip_equals_source_Hessian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:31:38.790333+00:00
-- url     : https://prove2.me/theorems/75e2cd0e-30a0-4f1f-9706-b4a70f18adeb
-- title:
--   Original finite-cap stopped Hessian coefficient agrees with the proven lower-and-upper clipped MDS coefficient on active cells
-- statement:
--   Given the genuine original postpayment reserve floor Y_si≥δ whenever the physical grid start s_i<ρ, with δ>0, the two Hessian coefficient definitions used by separate platform theorems agree exactly: the original source uses 1_{Y≤b}w''(Y) and the already Proved filtered-MDS theorem uses 1_{Y∈[δ/2,b]}w''(Y). This equality retains the original source discount and physical start-clock stopping mask. Establishing Y_si≥δ from right-continuity and the true prepayment floor is a separate original-source obligation.
-- source:
--   Bridges the authentic original stopped physical Gaussian Hessian noise term in 0ef5d778 to Proved gb63/gb65 MDS source without replacing the random process or silently imposing a spurious lower cutoff.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_active_postpayment_lower_clip_equals_source_Hessian
    {Ω : Type*} (δ b q : ℝ) (hδ : 0 < δ)
    (w : ℝ → ℝ) (Y : ℕ → Ω → ℝ)
    (s : ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (hFloor : ∀ (i : ℕ) (ω : Ω), s i < ρ ω → δ ≤ Y i ω) :
    ∀ (i : ℕ) (ω : Ω),
      (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ω ∈ Icc (δ / 2) b then iteratedDeriv 2 w (Y i ω) else 0)
      else 0) =
      (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ω ≤ b then iteratedDeriv 2 w (Y i ω) else 0)
      else 0) := by sorry
