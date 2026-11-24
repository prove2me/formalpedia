-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_exists_shape
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.exists_shape
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:57.971301+00:00
-- url     : https://prove2.me/theorems/016654c7-90e3-4796-a9da-628dc0c3b0a5
-- title:
--   Branch: exists shape
-- statement:
--   The Branch construction uses the exists shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L286-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L286-L330

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.exists_shape {n : ℕ} {μ : Fin (n + 1) → ℤ} (hμ : Antitone μ) (h : ℤ → ℕ)
    (hanti : ∀ c, h (c + 1) ≤ h c) (h1 : ∀ c, h c ≤ colHeight μ c) (h2 : ∀ c, colHeight μ c ≤ h c + 1)
    (h3 : ∀ c, h c ≤ n) : ∃ κ ∈ gtBox μ, ∀ c, h c = colHeight κ c := by sorry
