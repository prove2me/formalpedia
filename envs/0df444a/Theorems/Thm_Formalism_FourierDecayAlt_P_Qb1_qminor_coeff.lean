-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_qminor_coeff
-- name    : Formalism.FourierDecayAlt.P.Qb1.qminor_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:20:22.095745+00:00
-- url     : https://prove2.me/theorems/82b27fc9-7ef5-4767-b126-a6687f137441
-- title:
--   Qb1: qminor coeff
-- statement:
--   The Qb1 construction uses the qminor coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L158-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L158-L184

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

theorem Formalism.FourierDecayAlt.P.Qb1.qminor_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {w : Vs} (hw : SV σ w) {g : Mx k r} (hg : g ∈ GV k r) :
    qminorOp (EH k r) a b u (fun x => ℓ (σ x w)) g =
      ℓ (σ g (qmF (fun a b => EcRep (Hpk k r) σ (Matrix.single a b 1)) a b u w)) := by sorry
