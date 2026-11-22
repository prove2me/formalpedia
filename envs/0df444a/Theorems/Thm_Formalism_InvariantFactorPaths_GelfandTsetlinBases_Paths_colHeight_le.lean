-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:03.204283+00:00
-- url     : https://prove2.me/theorems/6422c085-749b-4d91-b8fa-f6b6b1c5f3ff
-- title:
--   Paths: col Height le
-- statement:
--   The Paths construction uses the col Height le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L43-L44

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_le {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : colHeight μ c ≤ n := by sorry
