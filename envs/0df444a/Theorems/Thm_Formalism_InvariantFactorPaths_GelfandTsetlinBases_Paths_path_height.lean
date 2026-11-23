-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_path_height
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.path_height
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:40.675709+00:00
-- url     : https://prove2.me/theorems/b76b973c-174e-4630-9ddf-fa91fe6c4f3b
-- title:
--   Paths: path height
-- statement:
--   The Paths construction uses the path height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L134-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L134-L148

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.path_height {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) {i : ℕ} (hi : i < N) (c : ℤ) :
    if isVec i then
      colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c = colHeight (μ i) c + 1
    else
      colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c + 1 = colHeight (μ i) c := by sorry
