-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_col_act
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.col_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:50.070581+00:00
-- url     : https://prove2.me/theorems/c65cbddd-c172-4abd-9ce6-debbe06070ca
-- title:
--   A3ev: col act
-- statement:
--   The A3ev construction uses the col act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L75-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L75-L139

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.col_act {L : Type} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (g : (Matrix (Fin n) (Fin n) L)ˣ) (N : ℕ) (J : Finset (Fin n)) :
    actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N J) =
      ∑ I' : Finset (Fin n),
        pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N I' *
          C (minorF (if 1 ≤ c then (↑g : Matrix (Fin n) (Fin n) L)
            else (↑g⁻¹ : Matrix (Fin n) (Fin n) L).transpose) I' J) := by sorry
