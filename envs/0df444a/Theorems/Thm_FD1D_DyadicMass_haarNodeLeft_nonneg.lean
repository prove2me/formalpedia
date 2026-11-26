-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarNodeLeft_nonneg
-- name    : FD1D.DyadicMass.haarNodeLeft_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:09.446747+00:00
-- url     : https://prove2.me/theorems/7706088a-9177-4f9f-b9f5-4472c72d705b
-- title:
--   Dyadic Mass: haar Node Left nonneg
-- statement:
--   The Dyadic Mass construction uses the haar Node Left nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1217-L1220
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1217-L1220

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass

theorem FD1D.DyadicMass.haarNodeLeft_nonneg {L : ℕ} (v : CompleteHaarNode L) :
    0 ≤ haarNodeLeft v := by sorry
