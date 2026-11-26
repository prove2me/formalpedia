-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarNodeRight_le_one
-- name    : FD1D.DyadicMass.haarNodeRight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:04.268887+00:00
-- url     : https://prove2.me/theorems/5295aa85-b016-57ca-be03-2b34324eeb13
-- title:
--   Dyadic Mass: haar Node Right le one
-- statement:
--   The Dyadic Mass construction uses the haar Node Right le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1222-L1229
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1222-L1229

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.haarNodeRight_le_one {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft v + haarNodeWidth v ≤ 1 := by sorry
