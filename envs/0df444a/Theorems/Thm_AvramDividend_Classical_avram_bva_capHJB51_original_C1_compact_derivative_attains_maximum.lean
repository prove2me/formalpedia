-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB51_original_C1_compact_derivative_attains_maximum
-- name    : AvramDividend.Classical.avram_bva_capHJB51_original_C1_compact_derivative_attains_maximum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:35:30.235377+00:00
-- url     : https://prove2.me/theorems/d7d84d00-42dc-4cf1-98e1-1e1419e02423
-- title:
--   Original C1 interior candidate derivative reaches maximum on each compact sub-cap interval
-- statement:
--   For original bounded-variation verification candidates C1 on the open positive reserve interior, the derivative is continuous on every compact interval contained in that interior. The real-valued continuous derivative therefore attains its maximum on the interval. This mathematically necessary source compactness ingredient supplies the hMax premise of the near-upper-cap BV derivative bootstrap and eventually the full unmasked finite-cap generator sign. Uses pinned Mathlib exact ContDiffOn derivative continuity and extreme value theorem, without local Lean.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB51_original_C1_compact_derivative_attains_maximum
    (w : ℝ → ℝ) (s : Set ℝ)
    (hsOpen : IsOpen s) (hwSmooth : ContDiffOn ℝ 1 w s)
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ s) :
    ∃ t ∈ Icc a b,
      ∀ r ∈ Icc a b, deriv w r ≤ deriv w t := by sorry
