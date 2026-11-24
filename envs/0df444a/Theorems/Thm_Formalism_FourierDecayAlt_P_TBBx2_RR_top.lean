-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_RR_top
-- name    : Formalism.FourierDecayAlt.P.TBBx2.RR_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:36.22771+00:00
-- url     : https://prove2.me/theorems/c162e51d-9f47-40ac-8a41-acd9128fbc2a
-- title:
--   TBBx2: RR top
-- statement:
--   The TBBx2 construction uses the RR top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L148-L153

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.TBBx2.RR_top (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR G (P.r + 1) [] γ γ = B.hsInner (p.V G γ) (p.V G γ) := by sorry
