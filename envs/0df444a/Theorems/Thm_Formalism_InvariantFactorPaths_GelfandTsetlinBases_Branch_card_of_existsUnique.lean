-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_card_of_existsUnique
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.card_of_existsUnique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:44.175178+00:00
-- url     : https://prove2.me/theorems/a933ba4f-fd73-444e-adf5-1a78f95ca40a
-- title:
--   Branch: card of exists Unique
-- statement:
--   The Branch construction uses the card of exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L390-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L390-L409

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.card_of_existsUnique {α β : Type*} (s : Finset β) (P : α → Prop) (Q : β → α → Prop)
    (h : ∀ a, P a → ∃ b ∈ s, Q b a)
    (hu : ∀ a b b', P a → b ∈ s → b' ∈ s → Q b a → Q b' a → b = b')
    (fin : ∀ b ∈ s, Finite {a // P a ∧ Q b a}) :
    Finite {a // P a} ∧ Nat.card {a // P a} = ∑ b ∈ s, Nat.card {a // P a ∧ Q b a} := by sorry
