-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_mem_span_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_span_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:55.377387+00:00
-- url     : https://prove2.me/theorems/f0c5df16-651b-4fea-a162-4a2bd09bc0a4
-- title:
--   GS: mem span iff
-- statement:
--   The GS construction uses the mem span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L95-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L95-L136

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_span_iff (N : Submodule k (MvPolynomial σ k)) (P : MvPolynomial σ A) :
    P ∈ Submodule.span A ((fun f => map (algebraMap k A) f) '' (N : Set (MvPolynomial σ k))) ↔
      slSpace (k := k) P ≤ N := by sorry
