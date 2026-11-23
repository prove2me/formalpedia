-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_pathWord_unchanged
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.pathWord_unchanged
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:31.516106+00:00
-- url     : https://prove2.me/theorems/5e003bd9-6562-455f-b4f2-2dbd0515f6dd
-- title:
--   Paths: path Word unchanged
-- statement:
--   The Paths construction uses the path Word unchanged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L190-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L190-L202

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.pathWord_unchanged {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ)
    (c : ℤ) (Xr : ℕ → Fin n → R) : ∀ j : ℕ,
    (∀ i < j, colHeight (μ (i + 1)) c = colHeight (μ i) c) →
      pathWord isVec μ c Xr j = oneF ∧ colHeight (μ j) c = colHeight (μ 0) c := by sorry
