-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonKernel_integrableOn_Ioi
-- name    : CohnElkies.stripPoissonKernel_integrableOn_Ioi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/3f03b664-9ea0-43a7-8d38-4508720fc5e6
-- title:
--   CohnElkies.stripPoissonKernel_integrableOn_Ioi
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
open scoped Interval Topology

theorem CohnElkies.stripPoissonKernel_integrableOn_Ioi {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    IntegrableOn (stripPoissonKernel σ) (Ioi (0 : ℝ)) := by sorry
