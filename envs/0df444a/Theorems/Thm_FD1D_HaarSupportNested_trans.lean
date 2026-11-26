-- Prove2me | Theorems.Thm_FD1D_HaarSupportNested_trans
-- name    : FD1D.HaarSupportNested.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:23.498731+00:00
-- url     : https://prove2.me/theorems/b61c3356-7ed7-59d0-9ae5-30a04684f60f
-- title:
--   Haar Support Nested: trans
-- statement:
--   The Haar Support Nested construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L917-L920
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L917-L920

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.HaarSupportNested.trans {L : ℕ} {u v w : CompleteHaarNode L}
    (huv : HaarSupportNested u v) (hvw : HaarSupportNested v w) :
    HaarSupportNested u w := by sorry
