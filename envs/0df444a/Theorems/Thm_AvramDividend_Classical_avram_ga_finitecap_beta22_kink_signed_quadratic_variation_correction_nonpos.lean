-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_finitecap_beta22_kink_signed_quadratic_variation_correction_nonpos
-- name    : AvramDividend.Classical.avram_ga_finitecap_beta22_kink_signed_quadratic_variation_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:40:02.594091+00:00
-- url     : https://prove2.me/theorems/bf5b1177-44e3-4521-a101-04ff7500808c
-- title:
--   Exact nonpositive Gaussian quadratic variation correction from a downward dividend cap kink after one-sided Beta smoothing
-- statement:
--   Under the original dividend-gradient condition α≥1, any Gaussian scale σ, and any positive smoothing width ε, the Gaussian quadratic variation correction (σ²/2)(1−α)Qε,b''(y) is nonpositive at every point away from the two smoothing transition levels. Qε,b is the explicit one-sided Beta(2,2) mollification of the positive cap hinge. This is the correctly signed physical upper-cap local-time correction for the finite-cap stopped Itô–Stieltjes verification route; it neither assumes the source stochastic ledger nor discards the required upper-cap drift occupation charge.
-- source:
--   The genuine original finitecap Gaussian cash estimate 0ef5d778 requires signed cap local-time correction. This proof combines the accepted exact Beta curvature identity with 1-α≤0; the separate fixed-level zero-occupation lemma handles boundary levels.

import Mathlib
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_finitecap_beta22_kink_signed_quadratic_variation_correction_nonpos
    (σ α b ε y : ℝ) (hε : 0 < ε) (hα : 1 ≤ α)
    (hb : y ≠ b) (hu : y ≠ b + ε) :
    (σ ^ 2 / 2) * (1 - α) *
      iteratedDeriv 2 (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y ≤ 0 := by sorry
