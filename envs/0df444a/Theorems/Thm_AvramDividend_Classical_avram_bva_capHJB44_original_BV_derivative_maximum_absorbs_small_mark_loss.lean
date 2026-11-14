-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB44_original_BV_derivative_maximum_absorbs_small_mark_loss
-- name    : AvramDividend.Classical.avram_bva_capHJB44_original_BV_derivative_maximum_absorbs_small_mark_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:26:12.766057+00:00
-- url     : https://prove2.me/theorems/f2d719fb-56ad-4189-9608-f4fde4ad7246
-- title:
--   Finite-cap original BV C1 maximum bootstrap absorbs the small-negative-jump first moment
-- statement:
--   For original bounded-variation source candidate differentiable on the positive cap interior, suppose the derivative reaches a maximum on each compact sub-cap band, its base compact derivative is bounded by B, and its interior HJB generator plus small jump first-moment decomposition bounds the positive drift times derivative by A plus eta times that compact maximum. If small-jump absolute first moment eta is strictly less than true physical positive drift d, all derivatives approaching finite upper cap are uniformly bounded by maximum of B and A/(d-eta). This is the central source localisation bootstrap needed for true closed-cap full-mark dominated convergence.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB44_original_BV_derivative_maximum_absorbs_small_mark_loss
    (d η A B ε c : ℝ) (hd : η < d)
    (hε : 0 < ε) (hc : ε < c)
    (w : ℝ → ℝ)
    (hLocal : ∀ t ∈ Icc (ε / 2) ε, deriv w t ≤ B)
    (hMax : ∀ b ∈ Ioo ε c,
      ∃ s ∈ Icc (ε / 2) b,
        ∀ t ∈ Icc (ε / 2) b, deriv w t ≤ deriv w s)
    (hEnv : ∀ b ∈ Ioo ε c,
      ∀ s ∈ Icc ε b,
      ∀ M : ℝ,
      (∀ t ∈ Icc (ε / 2) b, deriv w t ≤ M) →
      d * deriv w s ≤ A + η * M) :
    ∀ t ∈ Ico (ε / 2) c,
      deriv w t ≤ max B (A / (d - η)) := by sorry
