-- Prove2me | Theorems.Thm_FD1D_haarNodeTent_eq_zero_outside
-- name    : FD1D.haarNodeTent_eq_zero_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:29:00.137812+00:00
-- url     : https://prove2.me/theorems/e080159c-213f-4145-9f99-9c4599bc620a
-- title:
--   FD1 D: haar Node Tent eq zero outside
-- statement:
--   The FD1 D construction uses the haar Node Tent eq zero outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L912-L915
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L912-L915

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.haarNodeTent_eq_zero_outside {L : ℕ} (v : CompleteHaarNode L) {z : ℝ}
    (hz : z ∉ Icc (haarNodeLeft v) (haarNodeLeft v + haarNodeWidth v)) :
    haarNodeTent v z = 0 := by sorry
