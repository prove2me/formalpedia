-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_pathWord_congr
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.pathWord_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:52.535382+00:00
-- url     : https://prove2.me/theorems/3b652526-93f8-423b-a4d6-6cd10a1efcc7
-- title:
--   A1: path Word congr
-- statement:
--   The A1 construction uses the path Word congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L673-L682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L673-L682

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.pathWord_congr {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ μ' : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ∀ j, (∀ i ≤ j, μ i = μ' i) →
      pathWord isVec μ c Xr j = pathWord isVec μ' c Xr j := by sorry
