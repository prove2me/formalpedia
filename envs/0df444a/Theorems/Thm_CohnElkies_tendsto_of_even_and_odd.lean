-- Prove2me | Theorems.Thm_CohnElkies_tendsto_of_even_and_odd
-- name    : CohnElkies.tendsto_of_even_and_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.654547+00:00
-- url     : https://prove2.me/theorems/6ea9f991-adce-47dd-b54e-d4cd55e861e3
-- title:
--   CohnElkies.tendsto_of_even_and_odd
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
open Filter
open scoped Nat Topology

theorem CohnElkies.tendsto_of_even_and_odd {X : Type*} [TopologicalSpace X]
    {f : ℕ → X} {x : X}
    (heven : Tendsto (fun k : ℕ => f (2 * k)) atTop (nhds x))
    (hodd : Tendsto (fun k : ℕ => f (2 * k + 1)) atTop (nhds x)) :
    Tendsto f atTop (nhds x) := by sorry
