-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_zero_extension_global_monotone_of_secant
-- name    : AvramDividend.Classical.avram_wave6_08_zero_extension_global_monotone_of_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:09:32.806381+00:00
-- url     : https://prove2.me/theorems/00939620-485b-4bb8-8a78-fb4badaadaad
-- title:
--   Corrected zero-boundary positivity makes cap-linear dividend candidate globally monotone
-- statement:
--   A positive-reserve slope-one secant bound on [0,∞), the true source zero extension on negative reserves, and the corrected boundary nonnegativity V(0)≥0 together force global monotonicity across zero. This bridges the original Lévy ruin-jump terminal comparison V(R_ruin)≤V(Z_last) when R_ruin may be negative and Z_last≥R_ruin. The indispensable corrected boundary condition is actually used; no stochastic estimate is assumed.
-- source:
--   Corrected source-specific original UBV stopped terminal positive-ruin comparison, using the genuine global cap-linear secant a4675c8a and required w0≥0.

import Mathlib

open Filter Set

theorem AvramDividend.Classical.avram_wave6_08_zero_extension_global_monotone_of_secant
    (V : ℝ → ℝ) (hneg : ∀ y < 0, V y = 0)
    (h0 : 0 ≤ V 0)
    (hsec : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ V b - V a) :
    Monotone V := by sorry
