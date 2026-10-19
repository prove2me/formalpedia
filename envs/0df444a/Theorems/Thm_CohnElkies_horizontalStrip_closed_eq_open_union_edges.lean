-- Prove2me | Theorems.Thm_CohnElkies_horizontalStrip_closed_eq_open_union_edges
-- name    : CohnElkies.horizontalStrip_closed_eq_open_union_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/ba32db73-7bfb-400d-8349-58fa06455371
-- title:
--   CohnElkies.horizontalStrip_closed_eq_open_union_edges
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
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem CohnElkies.horizontalStrip_closed_eq_open_union_edges
    {a b : ℝ} (hab : a < b) :
    (Complex.im ⁻¹' Icc a b) =
      ((Complex.im ⁻¹' Ioo a b) ∪
        (Complex.im ⁻¹' {a})) ∪
        (Complex.im ⁻¹' {b}) := by sorry
