-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowW_apply
-- name    : Formalism.FourierDecayAlt.P.Ux2.lowW_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:53:29.948807+00:00
-- url     : https://prove2.me/theorems/c98e0d7f-a8c9-43bf-9e32-798cb7762b87
-- title:
--   Ux2: low W apply
-- statement:
--   The Ux2 construction uses the low W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L452-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L452-L454

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux2.lowW_apply (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a b : Fin p) :
    lowW σ v a b = (if a = b then 1 else 0) + (if h : b < a ∧ σ.symm b < σ.symm a then v ⟨(a, b), h⟩ else 0) := by sorry
