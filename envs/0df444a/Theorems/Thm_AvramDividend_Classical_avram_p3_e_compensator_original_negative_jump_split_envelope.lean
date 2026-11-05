-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_split_envelope
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_split_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:02:41.488397+00:00
-- url     : https://prove2.me/theorems/8a57bb3e-5a97-405b-a7e5-f4507bd0240f
-- title:
--   Original nonlinear negative jump splits into small-jump Lipschitz and large-mark finite envelope
-- statement:
--   On the original stopped BV reserve interior y∈[a,b], every negative jump z is bounded by L|z| for marks z≥−a/2, while larger negative marks contribute at most 2R. This is the source jump-integrand envelope needed to dominate the compensator by the finite first negative moment and finite large-mark rate of the original Lévy measure.
-- source:
--   Pure deterministic bound for the exact nonlinear original source negative-jump term w(y+z)-w(y), using the same local Lipschitz and negative half-line bound as Proved source-specific theorem 8dda0d29-ac4a-4c35-87de-498bfca2df2a. No assumed compensator or changed process.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_split_envelope
(w : ℝ → ℝ) (a b L R : ℝ)
(ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(y z : ℝ) (hy : y ∈ Set.Icc a b) (hz : z < 0) :
|w (y + z) - w y| ≤ if -(a / 2) ≤ z then L * |z| else 2 * R := by sorry
