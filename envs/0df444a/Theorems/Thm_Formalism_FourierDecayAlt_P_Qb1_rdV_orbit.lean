-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_rdV_orbit
-- name    : Formalism.FourierDecayAlt.P.Qb1.rdV_orbit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:20:43.563479+00:00
-- url     : https://prove2.me/theorems/66e4dc31-3067-4c70-bee9-4451e3bfc06b
-- title:
--   Qb1: rd V orbit
-- statement:
--   The Qb1 construction uses the rd V orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L83-L86

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

theorem Formalism.FourierDecayAlt.P.Qb1.rdV_orbit (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => σ x w) g = σ g (dRep σ X w) := by sorry
