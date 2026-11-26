-- Prove2me | Theorems.Thm_FD1D_globalHarmonicPotential_nonneg
-- name    : FD1D.globalHarmonicPotential_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:02.189346+00:00
-- url     : https://prove2.me/theorems/1a268056-dcaa-4138-ab26-c94fdf1d0b7c
-- title:
--   FD1 D: global Harmonic Potential nonneg
-- statement:
--   Every global harmonic potential is nonnegative.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L71-L80
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L71-L80

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.globalHarmonicPotential_nonneg
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) :
    0 ≤ globalHarmonicPotential L a N := by sorry
