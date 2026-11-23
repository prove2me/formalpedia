-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_sLe
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.mem_sLe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:38.141275+00:00
-- url     : https://prove2.me/theorems/3c8ba040-4ecd-4a64-8376-d3112b3e4cd6
-- title:
--   Pieri: mem s Le
-- statement:
--   The Pieri construction uses the mem s Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L66-L76

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.mem_sLe {n : ℕ} (κ l : Fin n → ℤ) (b : ℕ) :
    l ∈ sLe κ b ↔ (∀ m, κ m ≤ l m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) ∧
      ∑ m, l m - ∑ m, κ m ≤ (b : ℤ) := by sorry
