-- Prove2me | Theorems.Thm_BitDFT_rounding_bridge
-- name    : BitDFT.rounding_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:01:32.649199+00:00
-- url     : https://prove2.me/theorems/61507a72-b6f9-4651-a7e1-10e48f4ff5ff
-- title:
--   Integer-pair encoding agrees with existing complex rounding
-- statement:
--   For all precision parameters and complex inputs, interpreting the coordinatewise rounded integer pair at that precision equals the existing IntMul.HvdH.rho function. This links numerical and binary representations without asserting a runtime.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Section 2 — rounding representation.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.rounding_bridge (p : ℕ) (z : ℂ) :
    value p (roundPair p z) = IntMul.HvdH.rho p z := by sorry
