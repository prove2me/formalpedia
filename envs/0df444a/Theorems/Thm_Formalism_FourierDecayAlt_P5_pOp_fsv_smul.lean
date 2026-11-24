-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_pOp_fsv_smul
-- name    : Formalism.FourierDecayAlt.P5.pOp_fsv_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:41:24.094323+00:00
-- url     : https://prove2.me/theorems/e1e1bd94-905e-4137-a8c5-80e80ec0e8a5
-- title:
--   P5: p Op fsv smul
-- statement:
--   The P5 construction uses the p Op fsv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L68-L77

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
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

theorem Formalism.FourierDecayAlt.P5.pOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pOp l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • pOp l φ c + t • fsv t (c l) • (c l • φ c) := by sorry
