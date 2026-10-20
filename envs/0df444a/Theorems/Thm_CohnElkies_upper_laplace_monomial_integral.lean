-- Prove2me | Theorems.Thm_CohnElkies_upper_laplace_monomial_integral
-- name    : CohnElkies.upper_laplace_monomial_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/2cb66412-b02e-48c4-8e27-7c558d8b1d10
-- title:
--   CohnElkies.upper_laplace_monomial_integral
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

theorem CohnElkies.upper_laplace_monomial_integral
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (∫ a : ℝ in Set.Ioi 0,
      a ^ k * Real.exp (-η * a)) =
        (k.factorial : ℝ) / η ^ (k + 1) := by sorry
