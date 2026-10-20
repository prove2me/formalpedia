-- Prove2me | Theorems.Thm_ConnesRigidity_gamma_pairwise_nonisomorphic
-- name    : ConnesRigidity.gamma_pairwise_nonisomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/d956f90f-1aeb-4fee-a4bd-b07aa95b4850
-- title:
--   ConnesRigidity.gamma_pairwise_nonisomorphic
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | ConnesRigidity | external Lean 4.33.1 validation; bundle SHA256 4ed9232ec35753a258ad689b720fbf6aae9317c7cf506b5797de1710cec6f4a3

import Mathlib
import Definitions.Def_ConnesRigidity
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
open ConnesRigidity

theorem ConnesRigidity.gamma_pairwise_nonisomorphic {m n : ℕ} (hmn : m ≠ n) :
    ¬GroupsIsomorphic (gammaGroup m) (gammaGroup n) := by sorry
