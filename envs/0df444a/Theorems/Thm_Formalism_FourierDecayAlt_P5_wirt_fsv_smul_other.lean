-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_wirt_fsv_smul_other
-- name    : Formalism.FourierDecayAlt.P5.wirt_fsv_smul_other
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:28.134579+00:00
-- url     : https://prove2.me/theorems/74c5fc66-9e2b-47b5-ba62-3584a70537e7
-- title:
--   P5: wirt fsv smul other
-- statement:
--   The P5 construction uses the wirt fsv smul other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L158-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L158-L174

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

theorem Formalism.FourierDecayAlt.P5.wirt_fsv_smul_other (t : ℂ) {l l' : Fin m} (hl : l' ≠ l) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l' (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l' φ c ∧
    wirtBar l' (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirtBar l' φ c := by sorry
