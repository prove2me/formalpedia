-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_brk_eq
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.brk_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:03.129692+00:00
-- url     : https://prove2.me/theorems/ce44992f-1467-4a55-87f4-8b7b16dbead9
-- title:
--   Sign Twist Star Lemmas: brk eq
-- statement:
--   The Sign Twist Star Lemmas construction uses the brk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L251-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L251-L269

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.brk_eq {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) :
    brk (genMat k n) (genMat k n)⁻¹ μ I =
      (∏ c ∈ Finset.Ioc lo hi, sgnU k μ I c) •
        ((∏ c ∈ Finset.Ioc lo hi, if 1 ≤ c then (1 : GenField k n) else ((genMat k n).det)⁻¹) *
          algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)
            (tabMinors k (colT lo (hi - lo).toNat I))) := by sorry
