-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SpanImageLemmas_split
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas.split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:42.695592+00:00
-- url     : https://prove2.me/theorems/c9d060d2-b20d-5fa8-9e7e-572734ec2824
-- title:
--   Span Image Lemmas: split
-- statement:
--   The Span Image Lemmas construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/MemSpanImageIff.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/MemSpanImageIff.lean#L15-L24

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas.split {X R : Type} [CommRing R] (a : X →₀ R) (S : Set X) :
    ∃ a1 a2 : X →₀ R, a = a1 + a2 ∧ (∀ x ∉ S, a1 x = 0) ∧ (∀ x ∈ S, a2 x = 0) ∧ ∀ x ∉ S, a2 x = a x := by sorry
