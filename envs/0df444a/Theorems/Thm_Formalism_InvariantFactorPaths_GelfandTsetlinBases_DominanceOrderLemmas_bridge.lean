-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_DominanceOrderLemmas_bridge
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.bridge
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:23.092882+00:00
-- url     : https://prove2.me/theorems/02c3cda2-2320-4ec4-a863-06652f5ca5a1
-- title:
--   Dominance Order Lemmas: bridge
-- statement:
--   The Dominance Order Lemmas construction uses the bridge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GoodWOfWeight.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GoodWOfWeight.lean#L85-L94

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.bridge (k : Type) [Field k] {n N : ℕ} (isVec : ℕ → Bool) {G : MvPolynomial (ℕ × Fin n) k}
    (hv : ∀ x ∈ G.vars, x.1 < N) :
    rename Sum.inl (actAll isVec (genMat k n) (genMat k n)⁻¹ (map (algebraMap k (GenField k n)) G)) =
      genPoint (ζ := Empty) isVec {j : ℕ | j < N} (rename Sum.inl G) := by sorry
