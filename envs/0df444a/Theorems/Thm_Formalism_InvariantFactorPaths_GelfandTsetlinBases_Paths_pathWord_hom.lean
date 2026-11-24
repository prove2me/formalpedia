-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_pathWord_hom
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.pathWord_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:23.464068+00:00
-- url     : https://prove2.me/theorems/c2e575a5-e4c3-4785-b617-6f5d8f175e18
-- title:
--   Paths: path Word hom
-- statement:
--   The Paths construction uses the path Word hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L224-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean#L224-L262

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.pathWord_hom (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ)
    (c : ℤ) (i : ℕ) : ∀ (j : ℕ) (J : Finset (Fin n)),
    IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j J)
      (if i < j ∧ colHeight (μ (i + 1)) c ≠ colHeight (μ i) c then 1 else 0) := by sorry
