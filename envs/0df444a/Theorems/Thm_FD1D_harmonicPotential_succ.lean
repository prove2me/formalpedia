-- Prove2me | Theorems.Thm_FD1D_harmonicPotential_succ
-- name    : FD1D.harmonicPotential_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:49.633365+00:00
-- url     : https://prove2.me/theorems/5c2e1bf4-1b8b-5df6-a5f3-b18604b3c7be
-- title:
--   FD1 D: harmonic Potential succ
-- statement:
--   The FD1 D construction uses the harmonic Potential succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L24-L29
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L24-L29

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.harmonicPotential_succ (a : ℝ) (k : ℕ) :
    harmonicPotential a (k + 1) =
      harmonicPotential a k + 1 / (k + 1 + a) := by sorry
