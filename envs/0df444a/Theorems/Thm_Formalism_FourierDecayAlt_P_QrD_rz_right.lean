-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_rz_right
-- name    : Formalism.FourierDecayAlt.P.QrD.rz_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:06.269641+00:00
-- url     : https://prove2.me/theorems/a55b0e0e-9d4e-406a-aea5-50d92dc344f8
-- title:
--   Qr D: rz right
-- statement:
--   The Qr D construction uses the rz right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L158-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L158-L168

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem Formalism.FourierDecayAlt.P.QrD.rz_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((ecOp π' Z).comp B) := by sorry
