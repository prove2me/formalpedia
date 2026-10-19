-- Prove2me | Theorems.Thm_CohnElkies_saddleGaussianOuterPhi_le_endpointBarrier
-- name    : CohnElkies.saddleGaussianOuterPhi_le_endpointBarrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.736036+00:00
-- url     : https://prove2.me/theorems/efc3e783-573e-46f8-87b5-811a88632730
-- title:
--   CohnElkies.saddleGaussianOuterPhi_le_endpointBarrier
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
open Filter Set MeasureTheory
open scoped Topology

theorem CohnElkies.saddleGaussianOuterPhi_le_endpointBarrier
    {B Q c ℓ δ₀ δ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hℓ : 0 ≤ ℓ) (hδ₀ : 0 ≤ δ₀) (hδ : δ₀ ≤ δ)
    (hscale :
      (B + 1) / 2 + 4 ≤
        c * ℓ * Q * B * Real.exp (B * δ₀)) :
    saddleGaussianOuterPhi B Q c ℓ δ ≤
      ((B + 1) / 2 + 4) * δ₀ + 4 -
        c * ℓ * Q * Real.exp (B * δ₀) := by sorry
