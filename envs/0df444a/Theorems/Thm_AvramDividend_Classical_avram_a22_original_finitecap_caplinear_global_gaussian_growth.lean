-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_caplinear_global_gaussian_growth
-- name    : AvramDividend.Classical.avram_a22_original_finitecap_caplinear_global_gaussian_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:17:14.556479+00:00
-- url     : https://prove2.me/theorems/baa9160f-a33a-45e0-816c-71bf69187a53
-- title:
--   Original finitecap HJB candidate has global linear-growth caplinear continuation
-- statement:
--   Under precisely the original finite-cap HJB continuity assumption on nonnegative reserves and original w=0 on negative reserves, construct a finite K≥0 for which the cap-linear continuation has global envelope |V(z)|≤K+|z| for every z. Compactness gives the bound on [0,b]; above cap V has exact slope one, and below zero raw w vanishes. This is an honest original Gaussian stopped crossing UI/L1 envelope, avoiding false global boundedness and using no unregulated above-cap HJB derivatives.
-- source:
--   True original caplinear continuation gaussian-crossing envelope from compact reserve w continuity; no stochastic mean source imported.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a22_original_finitecap_caplinear_global_gaussian_growth
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ,
      |if z ≤ b then w z else w b + (z - b)| ≤ K + |z| := by sorry
