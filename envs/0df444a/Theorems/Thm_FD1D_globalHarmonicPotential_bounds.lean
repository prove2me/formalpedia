-- Prove2me | Theorems.Thm_FD1D_globalHarmonicPotential_bounds
-- name    : FD1D.globalHarmonicPotential_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:23:35.046265+00:00
-- url     : https://prove2.me/theorems/cc623e34-bfcb-4f93-a34b-426f3c9ad390
-- title:
--   FD1 D: global Harmonic Potential bounds
-- statement:
--   The two-sided global potential estimate used in the transient argument.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L128-L135
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L128-L135

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.globalHarmonicPotential_bounds
    {L m : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) (hN : ∀ d v, N d v ≤ m) :
    0 ≤ globalHarmonicPotential L a N ∧
      globalHarmonicPotential L a N ≤
        Real.log (1 + (m : ℝ) / a) := by sorry
