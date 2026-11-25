-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_foldr_smulC
-- name    : Formalism.FourierDecayAlt.P5.foldr_smulC
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:32.193382+00:00
-- url     : https://prove2.me/theorems/45c33c0b-741e-47f9-8c61-ae97fe297e25
-- title:
--   P5: foldr smul C
-- statement:
--   The P5 construction uses the foldr smul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L60-L70

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
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P5.foldr_smulC (Ts : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (h : ∀ T ∈ Ts, SmulC T) : SmulC (fun f => Ts.foldr (fun T h => T h) f) := by sorry
