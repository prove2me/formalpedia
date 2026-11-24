-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_RR_top
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Tri.RR_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:07:27.509417+00:00
-- url     : https://prove2.me/theorems/d0d477f2-8312-4143-9bc9-c724eae37ee6
-- title:
--   Tri: RR top
-- statement:
--   The Tri construction uses the RR top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L267-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L267-L269

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

theorem Formalism.FourierDecayAlt.P.TBBx2.Tri.RR_top (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) : p.RR F (P.r + 1) [] γ γ = B.hsInner (p.V F γ) (p.V F γ) := by sorry
