-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_le_iff_lt_colHeight
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.le_iff_lt_colHeight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:00.485835+00:00
-- url     : https://prove2.me/theorems/638317e8-3d54-4863-9a67-e5fb4e9b9fa6
-- title:
--   Paths: le iff lt col Height
-- statement:
--   The Paths construction uses the le iff lt col Height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L19-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L19-L41

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.le_iff_lt_colHeight {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) (c : ℤ) (m : Fin n) :
    c ≤ μ m ↔ m.val < colHeight μ c := by sorry
