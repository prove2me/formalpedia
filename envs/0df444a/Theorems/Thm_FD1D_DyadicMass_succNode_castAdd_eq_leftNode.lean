-- Prove2me | Theorems.Thm_FD1D_DyadicMass_succNode_castAdd_eq_leftNode
-- name    : FD1D.DyadicMass.succNode_castAdd_eq_leftNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:27.664481+00:00
-- url     : https://prove2.me/theorems/b4980bff-172d-484a-8dba-145207dec646
-- title:
--   Dyadic Mass: succ Node cast Add eq left Node
-- statement:
--   The Dyadic Mass construction uses the succ Node cast Add eq left Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L978-L982
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L978-L982

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass

theorem FD1D.DyadicMass.succNode_castAdd_eq_leftNode {L : ℕ} (d : Fin L)
    (v : Fin (2 ^ d.val)) :
    (⟨d.succ, childFinEquiv d.val (Fin.castAdd (2 ^ d.val) v)⟩ :
      CompleteHaarNode (L + 1)) = leftNode ⟨d, v⟩ := by sorry
