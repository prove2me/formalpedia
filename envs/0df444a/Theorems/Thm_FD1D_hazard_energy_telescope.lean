-- Prove2me | Theorems.Thm_FD1D_hazard_energy_telescope
-- name    : FD1D.hazard_energy_telescope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:48:40.713799+00:00
-- url     : https://prove2.me/theorems/6b3cb60c-6694-51ae-9e0d-da523ab7f274
-- title:
--   FD1 D: hazard energy telescope
-- statement:
--   Exact hazard-energy telescope behind equations (1) and (2).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L435-L442
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L435-L442

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.hazard_energy_telescope
    (h : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) =
      hazardEnergy h L - hazardEnergy h 0 := by sorry
