-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_succ_le_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.Lo_succ_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:13.410666+00:00
-- url     : https://prove2.me/theorems/868a6f72-861c-41fc-b2ed-3c758d4a7219
-- title:
--   Pieri: Lo succ le iff
-- statement:
--   The Pieri construction uses the Lo succ le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L140-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L140-L162

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.Lo_succ_le_iff {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) :
    (∀ i : Fin n, Lo μ l i.succ ≤ κ i) ↔
      (∀ i : Fin n, μ i.succ ≤ κ i) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) := by sorry
