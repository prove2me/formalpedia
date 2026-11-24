-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_colT_inj
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.colT_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:05.06495+00:00
-- url     : https://prove2.me/theorems/5001c29a-7357-401a-9a66-94ab5a18c003
-- title:
--   Sign Twist Star Lemmas: col T inj
-- statement:
--   The Sign Twist Star Lemmas construction uses the col T inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L279-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L279-L291

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
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
open SignTwistStarLemmas
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.colT_inj {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I I' : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (hI' : IsIndex μ I')
    (h : colT lo (hi - lo).toNat I = colT lo (hi - lo).toNat I') : I = I' := by sorry
