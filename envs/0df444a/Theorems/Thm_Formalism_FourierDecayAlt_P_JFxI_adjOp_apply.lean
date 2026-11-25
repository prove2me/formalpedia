-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_adjOp_apply
-- name    : Formalism.FourierDecayAlt.P.JFxI.adjOp_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:33:31.854817+00:00
-- url     : https://prove2.me/theorems/592dc8d1-49b9-56e0-a24b-2eb23ee42169
-- title:
--   JFx I: adj Op apply
-- statement:
--   The JFx I construction uses the adj Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L277-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L277-L309

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.JFxI.adjOp_apply (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (Om k r D.z D.z') Θ)
    (f : Mat k r → (Wq →L[ℂ] Wp)) (hf : CkOn (opOrder Θ : ℕ∞) (Om k r D.z D.z') f) (g : Mat k r)
    (hg : g ∈ Om k r D.z D.z') : opApply (adjOp Θ) f g = opAdj Θ f g := by sorry
