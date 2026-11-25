-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_opL_fsv_smul_other
-- name    : Formalism.FourierDecayAlt.P5.opL_fsv_smul_other
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:12.619103+00:00
-- url     : https://prove2.me/theorems/02e9ddfc-7365-51f0-8e23-9f9e285ca718
-- title:
--   P5: op L fsv smul other
-- statement:
--   The P5 construction uses the op L fsv smul other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L176-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L176-L195

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P5.opL_fsv_smul_other (t : ℂ) {l l' : Fin m} (hl : l' ≠ l) (i : Fin 6) (φ : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) :
    opL l' i (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • opL l' i φ c := by sorry
