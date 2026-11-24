-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_Ew_top
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:48.12883+00:00
-- url     : https://prove2.me/theorems/51481499-dfe9-4150-916e-b4dea97ea561
-- title:
--   Tri: Ew top
-- statement:
--   The Tri construction uses the Ew top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L271-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L271-L278

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Tri
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par}

theorem Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew p (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (p.V F γ)‖ ^ 2 := by sorry
