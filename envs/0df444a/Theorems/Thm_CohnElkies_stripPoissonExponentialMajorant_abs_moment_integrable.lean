-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonExponentialMajorant_abs_moment_integrable
-- name    : CohnElkies.stripPoissonExponentialMajorant_abs_moment_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/212db3ed-7ccd-4756-96d0-86b8ec81d00e
-- title:
--   CohnElkies.stripPoissonExponentialMajorant_abs_moment_integrable
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
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.stripPoissonExponentialMajorant_abs_moment_integrable :
    Integrable (fun T : ℝ =>
      stripPoissonExponentialMajorant T * |T|) := by sorry
