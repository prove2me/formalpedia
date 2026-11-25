-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_ld_left
-- name    : Formalism.FourierDecayAlt.P.QrD.ld_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:55:51.007525+00:00
-- url     : https://prove2.me/theorems/edc3cbf5-b788-4a9a-8e93-b666dcb6be81
-- title:
--   Qr D: ld left
-- statement:
--   The Qr D construction uses the ld left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftTypeAction.lean#L51-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftTypeAction.lean#L51-L72

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftTypeAction
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
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem Formalism.FourierDecayAlt.P.QrD.ld_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : LdV X F g = (B.comp (dOp π X)).comp (J g) := by sorry
