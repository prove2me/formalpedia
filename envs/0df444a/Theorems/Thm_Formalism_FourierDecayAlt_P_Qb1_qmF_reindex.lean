-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_qmF_reindex
-- name    : Formalism.FourierDecayAlt.P.Qb1.qmF_reindex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:19.501613+00:00
-- url     : https://prove2.me/theorems/e286aef5-1ddc-498e-93cc-3a99914e0623
-- title:
--   Qb1: qm F reindex
-- statement:
--   The Qb1 construction uses the qm F reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L186-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L186-L193

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

theorem Formalism.FourierDecayAlt.P.Qb1.qmF_reindex {X : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ} (Eop : Fin n → Fin n → X → X) (u : ℂ) (x : X) :
    ∀ (t : ℕ) (h : t = n) (a : Fin t → Fin n), (∀ j, (a j).val = j.val) →
      qmF Eop a a u x = qmF Eop (id : Fin n → Fin n) id u x := by sorry
