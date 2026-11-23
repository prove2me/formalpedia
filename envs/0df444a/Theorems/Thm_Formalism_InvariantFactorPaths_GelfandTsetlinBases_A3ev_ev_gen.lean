-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_ev_gen
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.ev_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:20.550797+00:00
-- url     : https://prove2.me/theorems/b612f79d-dd04-42b0-8af8-5be6615848df
-- title:
--   A3ev: ev gen
-- statement:
--   The A3ev construction uses the ev gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L322-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L322-L333

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.ev_gen (hEV : FactEV) (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    (∀ ν : Fin n → ℤ,
      weightedHomogeneousComponent (torusW isVec) ν
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) ≠ 0 →
      DomLe ν (μ N)) ∧
    weightedHomogeneousComponent (torusW isVec) (μ N)
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) =
      C (brk (genMat k n) (genMat k n)⁻¹ (μ N) I) *
        psiPath (GenField k n) isVec μ N (canIdx (μ N)) := by sorry
