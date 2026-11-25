-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_mem_right
-- name    : Formalism.FourierDecayAlt.P.QrD.mem_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:27.708844+00:00
-- url     : https://prove2.me/theorems/e407a966-b19e-4b99-bd89-1decb4c08be2
-- title:
--   Qr D: mem right
-- statement:
--   The Qr D construction uses the mem right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L105-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L105-L119

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem Formalism.FourierDecayAlt.P.QrD.mem_right (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r (Fin.last r) ∩ D := by sorry
