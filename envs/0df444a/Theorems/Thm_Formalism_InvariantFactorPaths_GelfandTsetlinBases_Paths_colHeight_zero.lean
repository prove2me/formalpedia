-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_zero
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:32.013743+00:00
-- url     : https://prove2.me/theorems/05ecc75c-8173-4fe2-bf52-4bba4dad2b5e
-- title:
--   Paths: col Height zero
-- statement:
--   The Paths construction uses the col Height zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L46-L56

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_zero (n : ℕ) (c : ℤ) : colHeight (0 : Fin n → ℤ) c = if 1 ≤ c then 0 else n := by sorry
