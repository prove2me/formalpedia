-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_DominanceOrderLemmas_vars_actX
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.vars_actX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:21.902997+00:00
-- url     : https://prove2.me/theorems/9fdcfca3-e24d-4541-aac9-2831a25cc72b
-- title:
--   Dominance Order Lemmas: vars act X
-- statement:
--   The Dominance Order Lemmas construction uses the vars act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GoodWOfWeight.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GoodWOfWeight.lean#L46-L56

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.vars_actX {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    ∀ y ∈ (actAll isVec g gi (X x)).vars, y.1 = x.1 := by sorry
