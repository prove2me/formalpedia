-- Prove2me | Theorems.Thm_FD1D_globalHarmonicPotential_le_log_one_add
-- name    : FD1D.globalHarmonicPotential_le_log_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:36.778312+00:00
-- url     : https://prove2.me/theorems/da3e00de-136d-4394-9eb6-3ec8a6ce2b81
-- title:
--   FD1 D: global Harmonic Potential le log one add
-- statement:
--   If all node counts are at most `m`, then the global potential is at most
--   `log (1 + m/a)`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L86-L125
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L86-L125

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.globalHarmonicPotential_le_log_one_add
    {L m : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) (hN : ∀ d v, N d v ≤ m) :
    globalHarmonicPotential L a N ≤
      Real.log (1 + (m : ℝ) / a) := by sorry
