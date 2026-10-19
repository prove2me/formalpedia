-- Prove2me | Theorems.Thm_CohnElkies_upperGammaCenteredTruncatedKernel_eq_sum
-- name    : CohnElkies.upperGammaCenteredTruncatedKernel_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/181853fa-d7da-4b89-86de-bdd907f8ca1e
-- title:
--   CohnElkies.upperGammaCenteredTruncatedKernel_eq_sum
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

theorem CohnElkies.upperGammaCenteredTruncatedKernel_eq_sum
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaCenteredTruncatedKernel ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCenteredLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by sorry
