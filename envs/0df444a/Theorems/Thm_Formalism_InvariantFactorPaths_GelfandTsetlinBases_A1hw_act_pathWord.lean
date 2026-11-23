-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_act_pathWord
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.act_pathWord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:20.020278+00:00
-- url     : https://prove2.me/theorems/743a0dfa-4e6b-45b2-98b3-cbd02b854293
-- title:
--   A1hw: act path Word
-- statement:
--   The A1hw construction uses the act path Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L122-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L122-L142

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.act_pathWord (hw : FactX2wedge) (hc : FactX2contr) {A : Type} [CommRing A] {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xc Xe : ℕ → Fin n → A)
    (g : (Matrix (Fin n) (Fin n) A)ˣ)
    (h1 : ∀ i, (isVec i == decide (1 ≤ c)) = true → Xe i = Matrix.vecMul (Xc i) (↑g : Matrix _ _ A))
    (h2 : ∀ i, (isVec i == decide (1 ≤ c)) = false →
      Xe i = Matrix.vecMul (Xc i) (↑g⁻¹ : Matrix _ _ A).transpose) :
    ∀ j : ℕ, pathWord isVec μ c Xe j = actF (pathWord isVec μ c Xc j) (↑g : Matrix _ _ A) := by sorry
