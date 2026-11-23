-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_contr_term
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.contr_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:14.61421+00:00
-- url     : https://prove2.me/theorems/75af8311-adf3-420d-b77f-c3d42357cd92
-- title:
--   A1: contr term
-- statement:
--   The A1 construction uses the contr term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L213-L220

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
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.contr_term (w : ℕ × Fin n → M) (K : Form (MvPolynomial (ℕ × Fin n) R) n)
    (hK : ∀ J, IsWeightedHomogeneous w (K J) 0) (j : ℕ) (I : Finset (Fin n)) (m : Fin n) :
    IsWeightedHomogeneous w (((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * XR R n j m * K (insert m I))
      (w (j, m)) := by sorry
