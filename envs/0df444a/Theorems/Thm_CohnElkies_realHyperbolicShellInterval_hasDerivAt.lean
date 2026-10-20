-- Prove2me | Theorems.Thm_CohnElkies_realHyperbolicShellInterval_hasDerivAt
-- name    : CohnElkies.realHyperbolicShellInterval_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/a559aa94-a107-4677-a64c-10dbe288da67
-- title:
--   CohnElkies.realHyperbolicShellInterval_hasDerivAt
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

theorem CohnElkies.realHyperbolicShellInterval_hasDerivAt
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∫ x in a..b,
        w x * (Real.cosh (x * v) - 1))
      (∫ x in a..b,
        w x * x * Real.sinh (x * u)) u := by sorry
