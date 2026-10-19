-- Prove2me | Theorems.Thm_CohnElkies_complexWallisLogPrimitive_hasDerivAt
-- name    : CohnElkies.complexWallisLogPrimitive_hasDerivAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.348956+00:00
-- url     : https://prove2.me/theorems/eed50c98-6108-4834-b816-378b8cbc4303
-- title:
--   CohnElkies.complexWallisLogPrimitive_hasDerivAt
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

theorem CohnElkies.complexWallisLogPrimitive_hasDerivAt
    {z : ℂ} (hz : 0 < z.re)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ =>
        (z + (r : ℂ)) * Complex.log (z + (r : ℂ)) -
          (z + (r : ℂ)))
      (Complex.log (z + (s : ℂ))) s := by sorry
