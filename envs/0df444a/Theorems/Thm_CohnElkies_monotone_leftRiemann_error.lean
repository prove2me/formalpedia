-- Prove2me | Theorems.Thm_CohnElkies_monotone_leftRiemann_error
-- name    : CohnElkies.monotone_leftRiemann_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:53.711061+00:00
-- url     : https://prove2.me/theorems/d9fe1c24-f4a5-464b-a480-fc0ac7482706
-- title:
--   CohnElkies.monotone_leftRiemann_error
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
open scoped FourierTransform Interval RealInnerProductSpace Topology

theorem CohnElkies.monotone_leftRiemann_error
    (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ≤
        f 1 - f 0 := by sorry
