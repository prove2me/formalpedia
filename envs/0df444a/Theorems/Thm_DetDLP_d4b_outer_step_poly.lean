-- Prove2me | Theorems.Thm_DetDLP_d4b_outer_step_poly
-- name    : DetDLP.d4b_outer_step_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:07:37.458196+00:00
-- url     : https://prove2.me/theorems/547028f8-11b5-4c91-8f00-6e78f45fc109
-- title:
--   Polynomial time for one outer scalar-cursor transition
-- statement:
--   For every fixed small-instance threshold, the outer transition of the three-oracle scalar cursor is a polynomial-time function of its entire framed input, including when the supplied state or answer is malformed.

import Definitions.Def_DetDLP_D4BOuterStep
set_option autoImplicit false

theorem DetDLP.d4b_outer_step_poly : ∀ L₀ : ℕ, Groundwork.PolyT (DetDLP.outerStep L₀) := by sorry
