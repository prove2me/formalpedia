-- Prove2me | Theorems.Thm_FD1D_DyadicMass_succNode_natAdd_eq_rightNode
-- name    : FD1D.DyadicMass.succNode_natAdd_eq_rightNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:27.97817+00:00
-- url     : https://prove2.me/theorems/a4439bdd-05af-421b-b1e5-82bf0a388a54
-- title:
--   Dyadic Mass: succ Node nat Add eq right Node
-- statement:
--   The Dyadic Mass construction uses the succ Node nat Add eq right Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L984-L988
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L984-L988

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass

theorem FD1D.DyadicMass.succNode_natAdd_eq_rightNode {L : ℕ} (d : Fin L)
    (v : Fin (2 ^ d.val)) :
    (⟨d.succ, childFinEquiv d.val (Fin.natAdd (2 ^ d.val) v)⟩ :
      CompleteHaarNode (L + 1)) = rightNode ⟨d, v⟩ := by sorry
