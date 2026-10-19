-- Prove2me | Theorems.Thm_CohnElkies_upperGammaTruncatedDampingIntegrand_eq_sum
-- name    : CohnElkies.upperGammaTruncatedDampingIntegrand_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/9d026b50-7ea9-45be-8878-3d12b97d9da2
-- title:
--   CohnElkies.upperGammaTruncatedDampingIntegrand_eq_sum
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
open scoped Topology BigOperators

theorem CohnElkies.upperGammaTruncatedDampingIntegrand_eq_sum
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaTruncatedDampingIntegrand ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCosLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by sorry
