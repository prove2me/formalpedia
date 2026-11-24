-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SpanImageLemmas_basis
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas.basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:51.068102+00:00
-- url     : https://prove2.me/theorems/975e7f72-54c9-44ce-8ce7-d8d858768866
-- title:
--   Span Image Lemmas: basis
-- statement:
--   The Span Image Lemmas construction uses the basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/MemSpanImageIff.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/MemSpanImageIff.lean#L28-L31

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_MemSpanImageIff
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
variable {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas.basis (hc : CountPAll) (h2 : PathBasisOfCount) (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) :
    LinearIndependent R (psiFam R n N isVec B) ∧
      Submodule.span R (Set.range (psiFam R n N isVec B)) = polB R n N B := by sorry
