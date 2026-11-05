-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_original_subcap_V_to_w_increment
-- name    : AvramDividend.Classical.avram_p2_assist_p3_original_subcap_V_to_w_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:45:38.087182+00:00
-- url     : https://prove2.me/theorems/daca71ef-582f-4368-89f3-09cfef03f9a8
-- title:
--   Exact original cap-extended value increment agrees with w on every subcap frozen grid cell
-- statement:
--   For a finite or infinite cap, a source-frozen physical grid cell on which both reserve endpoints stay below the finite cap has the exact V-to-w increment equality required in the already Proved P3-F original physical C1 grid theorem 5341265a. The infinite-cap case is automatic. Outside the subcap strip the accepted full cap-overshoot increment 16088056 supplies the correct replacement, rather than asserting a false cross-cap identity.
-- source:
--   Algebraic case split on infinite cap and finite-cap endpoint localisation, using the exact V representation provided by P3-F; no stochastic hypotheses or strengthened result are assumed.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_original_subcap_V_to_w_increment
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ)
    (hStay : C ≠ ⊤ →
      z ≤ C.toReal ∧ z + d ≤ C.toReal) :
    V (z + d) - V z = w (z + d) - w z := by sorry
