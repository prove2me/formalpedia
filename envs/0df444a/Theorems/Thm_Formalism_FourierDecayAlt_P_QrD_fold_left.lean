-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_fold_left
-- name    : Formalism.FourierDecayAlt.P.QrD.fold_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:56:23.862804+00:00
-- url     : https://prove2.me/theorems/60267faf-9c69-44b3-9383-33fc2f20367d
-- title:
--   Qr D: fold left
-- statement:
--   The Qr D construction uses the fold left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftTypeAction.lean#L86-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftTypeAction.lean#L86-L108

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

theorem Formalism.FourierDecayAlt.P.QrD.fold_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z (hpart1 (Hpk k r) p.2) ∧ InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by sorry
