-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_sum_sub_prod
-- name    : Formalism.FourierDecayAlt.P.MeanNormSquaredBound.sum_sub_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:42.767792+00:00
-- url     : https://prove2.me/theorems/f0716e9e-865a-49ef-9521-01067b11db20
-- title:
--   Mean Norm Squared Bound: sum sub prod
-- statement:
--   The Mean Norm Squared Bound construction uses the sum sub prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanNormSquaredBound.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanNormSquaredBound.lean#L63-L67

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

theorem Formalism.FourierDecayAlt.P.MeanNormSquaredBound.sum_sub_prod {α β M : Type} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (f : α × β → M) : ∑ p : ↥A × ↥B, f (p.1.1, p.2.1) = ∑ p ∈ A ×ˢ B, f p := by sorry
