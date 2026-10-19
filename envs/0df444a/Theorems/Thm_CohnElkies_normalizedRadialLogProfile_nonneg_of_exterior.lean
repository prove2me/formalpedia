-- Prove2me | Theorems.Thm_CohnElkies_normalizedRadialLogProfile_nonneg_of_exterior
-- name    : CohnElkies.normalizedRadialLogProfile_nonneg_of_exterior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:51.566518+00:00
-- url     : https://prove2.me/theorems/5bd0ee4b-0632-4fe5-8948-7f9122ea630f
-- title:
--   CohnElkies.normalizedRadialLogProfile_nonneg_of_exterior
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
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem CohnElkies.normalizedRadialLogProfile_nonneg_of_exterior
    {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hnonzero : g ≠ 0) {R : ℝ} (hR : 0 < R)
    (houtside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → 0 ≤ (g x).re)
    (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ normalizedRadialLogProfile hd g R v := by sorry
