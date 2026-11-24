-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Ew_cut
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Ew_cut
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:02.244812+00:00
-- url     : https://prove2.me/theorems/03fca343-0172-463e-a0bb-f846059786bf
-- title:
--   TBBx2: Ew cut
-- statement:
--   The TBBx2 construction uses the Ew cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L159-L164

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

theorem Formalism.FourierDecayAlt.P.TBBx2.Ew_cut (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hV : TBB.VecCutAt p χ F) (ε : ℝ) (hε : 0 < ε) (γ : C.LPt) (hγ : D.IsLocPt γ (P.r + 1))
    (hG : ε ≤ TBB.Gp p γ) :
    TBB.Ew p nn (D.cutF p.T.base χ F ε) (P.r + 1) [] γ = TBB.Ew p nn F (P.r + 1) [] γ := by sorry
