-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_unitB_conj_mulVec
-- name    : Formalism.FourierDecayAlt.P.QrD.unitB_conj_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:36:36.78029+00:00
-- url     : https://prove2.me/theorems/ca41d44f-d189-4678-bafb-58d03c116dd3
-- title:
--   Qr D: unit B conj mul Vec
-- statement:
--   The Qr D construction uses the unit B conj mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L28-L36

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.QrD.unitB_conj_mulVec {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ) (a b : Fin m)
    (v : Fin n → ℂ) (h : herm H v (Bs a) = 0) : (unitB H Bs a b)ᴴ *ᵥ (H *ᵥ v) = 0 := by sorry
