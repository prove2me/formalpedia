-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_rdV_coeff
-- name    : Formalism.FourierDecayAlt.P.Qb1.rdV_coeff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:20:39.832103+00:00
-- url     : https://prove2.me/theorems/a6989846-2062-4f81-b5b3-54a60e78e35c
-- title:
--   Qb1: rd V coeff
-- statement:
--   The Qb1 construction uses the rd V coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L88-L92

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

theorem Formalism.FourierDecayAlt.P.Qb1.rdV_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) (ℓ : Vs →L[ℂ] ℂ) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => ℓ (σ x w)) g = ℓ (σ g (dRep σ X w)) := by sorry
