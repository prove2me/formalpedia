-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_DominanceOrderLemmas_actAll_X
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.actAll_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:30.17085+00:00
-- url     : https://prove2.me/theorems/c66b9f8d-1a1c-4108-a57c-6eabe8e30ae5
-- title:
--   Dominance Order Lemmas: act All X
-- statement:
--   The Dominance Order Lemmas construction uses the act All X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GoodWOfWeight.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GoodWOfWeight.lean#L38-L44

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.actAll_X {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (g gi : Matrix (Fin n) (Fin n) L)
    (i : ℕ) (a : Fin n) :
    actAll isVec g gi (X (i, a)) =
      if isVec i then ∑ b, X (i, b) * C (g b a) else ∑ b, X (i, b) * C (gi a b) := by sorry
