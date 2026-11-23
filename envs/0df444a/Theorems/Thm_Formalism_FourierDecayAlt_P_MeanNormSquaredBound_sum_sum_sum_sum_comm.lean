-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_sum_sum_sum_sum_comm
-- name    : Formalism.FourierDecayAlt.P.MeanNormSquaredBound.sum_sum_sum_sum_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:14.748877+00:00
-- url     : https://prove2.me/theorems/8abdbd38-686f-481e-8a46-2e803674a71a
-- title:
--   Mean Norm Squared Bound: sum sum sum sum comm
-- statement:
--   The Mean Norm Squared Bound construction uses the sum sum sum sum comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanNormSquaredBound.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanNormSquaredBound.lean#L34-L45

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.MeanNormSquaredBound.sum_sum_sum_sum_comm {α β M : Type} [AddCommMonoid M] (P : Finset α) (H : Finset β)
    (f : α → α → β → β → M) :
    ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h' =
      ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' := by sorry
