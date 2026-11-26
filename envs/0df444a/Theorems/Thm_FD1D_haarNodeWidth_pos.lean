-- Prove2me | Theorems.Thm_FD1D_haarNodeWidth_pos
-- name    : FD1D.haarNodeWidth_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:07.322406+00:00
-- url     : https://prove2.me/theorems/a618e06d-26ae-43f0-b45d-1ed5c4e6ba40
-- title:
--   FD1 D: haar Node Width pos
-- statement:
--   The FD1 D construction uses the haar Node Width pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L903-L905
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L903-L905

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.haarNodeWidth_pos {L : ℕ} (v : CompleteHaarNode L) :
    0 < haarNodeWidth v := by sorry
