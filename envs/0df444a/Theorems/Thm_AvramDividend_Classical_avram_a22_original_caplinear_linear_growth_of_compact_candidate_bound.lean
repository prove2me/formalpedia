-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_caplinear_linear_growth_of_compact_candidate_bound
-- name    : AvramDividend.Classical.avram_a22_original_caplinear_linear_growth_of_compact_candidate_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:14:24.624248+00:00
-- url     : https://prove2.me/theorems/93083e60-a9fb-4537-86e5-aaacd9304bfd
-- title:
--   Original finitecap caplinear continuation grows at most linearly at Gaussian crossings
-- statement:
--   For an original HJB value candidate w vanishing strictly below zero and bounded in absolute value by K on the original finite-cap reserve interval [0,b], the cap-linear continuation V(z)=w(z) for z≤b and V(z)=w(b)+(z-b) for z>b satisfies the global linear-growth bound |V(z)|≤K+|z|. This supplies an honest Gaussian crossing integrability envelope without falsely assuming that caplinear V is globally bounded or that raw w above the cap obeys HJB. The existence of a finite K follows separately from the original continuousOn w [0,b] and compactness.
-- source:
--   Finitecap original stopped Gaussian crossing source: caplinear continuation global linear growth on all ℝ given the compact original candidate value envelope.

import Mathlib

theorem AvramDividend.Classical.avram_a22_original_caplinear_linear_growth_of_compact_candidate_bound
    (w : ℝ → ℝ) (b K : ℝ) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_bound : ∀ z : ℝ, 0 ≤ z → z ≤ b → |w z| ≤ K)
    (z : ℝ) :
    |if z ≤ b then w z else w b + (z - b)| ≤ K + |z| := by sorry
