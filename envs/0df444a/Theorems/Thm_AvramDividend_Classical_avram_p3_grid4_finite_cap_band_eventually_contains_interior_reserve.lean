-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:50:50.422509+00:00
-- url     : https://prove2.me/theorems/7df6597f-27e1-4fa1-a99b-5c794d0ad946
-- title:
--   Refining finite cap source bands eventually contain each strict interior reserve
-- statement:
--   For any finite positive cap c and any fixed positive interior reserve 0<y<c, the deterministic compact localisation with left radius d/(n+1) and right radius c(n+1)/(n+2) eventually contains y for all n. Take d=min(1,c/2) to recover the original BV finite-cap source bands. The new fact is genuine band exhaustion needed to justify localisation limits, and does not assume a stopped dividend/source identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve (c d y : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hy : 0 < y) (hyc : y < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc ((d / ((n : ℝ) + 1)) / 2)
        (c * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by sorry
