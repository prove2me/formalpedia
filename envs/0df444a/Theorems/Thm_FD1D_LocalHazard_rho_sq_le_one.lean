-- Prove2me | Theorems.Thm_FD1D_LocalHazard_rho_sq_le_one
-- name    : FD1D.LocalHazard.rho_sq_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:26.906397+00:00
-- url     : https://prove2.me/theorems/c670b24f-dcf2-5867-b3e4-c98a5208857a
-- title:
--   Local Hazard: rho sq le one
-- statement:
--   The Local Hazard construction uses the rho sq le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L202-L211
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L202-L211

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.rho_sq_le_one {x y : ℕ} (hne : x + y ≠ 0) : rho x y ^ 2 ≤ 1 := by sorry
