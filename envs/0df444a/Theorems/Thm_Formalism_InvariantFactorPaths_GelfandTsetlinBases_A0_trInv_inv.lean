-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_trInv_inv
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.trInv_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:46:49.967282+00:00
-- url     : https://prove2.me/theorems/9d1832c0-a03f-4aa0-bd5e-f8e1643d4912
-- title:
--   A0: tr Inv inv
-- statement:
--   The A0 construction uses the tr Inv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L24-L25

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.trInv_inv {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) :
    (↑(trInv m)⁻¹ : Matrix (Fin n) (Fin n) R) = (↑m : Matrix (Fin n) (Fin n) R).transpose := by sorry
