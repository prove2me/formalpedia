-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_colHeight_lo
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.colHeight_lo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:43.692904+00:00
-- url     : https://prove2.me/theorems/7bf319a1-467f-4659-a34c-eab0f87ddc42
-- title:
--   Sign Twist Star Lemmas: col Height lo
-- statement:
--   The Sign Twist Star Lemmas construction uses the col Height lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L166-L169

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.colHeight_lo {μ : Fin n → ℤ} {lo c : ℤ} (h : ∀ m, lo ≤ μ m) (hc : c ≤ lo) : colHeight μ c = n := by sorry
