-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_polyOp_append
-- name    : Formalism.FourierDecayAlt.P.CutMP.QMinOp.polyOp_append
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:31.876889+00:00
-- url     : https://prove2.me/theorems/f9360e5f-9fbe-5f8b-b7b7-020b82bcd2c2
-- title:
--   QMin Op: poly Op append
-- statement:
--   The QMin Op construction uses the poly Op append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatQMinOp.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatQMinOp.lean#L182-L188

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.CutMP.QMinOp.polyOp_append {o κ : ℕ} {Θ₁ Θ₂ : B.DiffOp k r Wp Wq} (h₁ : PolyOp o κ Θ₁) (h₂ : PolyOp o κ Θ₂) :
    PolyOp o κ (Θ₁ ++ Θ₂) := by sorry
