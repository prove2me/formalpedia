-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_stepV
-- name    : Formalism.FourierDecayAlt.P.Qb1.sv_stepV
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:10.873874+00:00
-- url     : https://prove2.me/theorems/5091a5f2-5eae-4fa1-99ea-22378dde7d75
-- title:
--   Qb1: sv step V
-- statement:
--   The Qb1 construction uses the sv step V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L111-L117

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem Formalism.FourierDecayAlt.P.Qb1.sv_stepV (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (c : ℂ) (a b : Fin (2 * r + k + 1)) :
    SV σ (stepV σ c a b w) := by sorry
