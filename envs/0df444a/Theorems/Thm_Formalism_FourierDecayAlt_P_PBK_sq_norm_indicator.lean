-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_sq_norm_indicator
-- name    : Formalism.FourierDecayAlt.P.PBK.sq_norm_indicator
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:18:06.788951+00:00
-- url     : https://prove2.me/theorems/faa0d072-7695-41ad-8359-a347883cadbd
-- title:
--   PBK: sq norm indicator
-- statement:
--   The PBK construction uses the sq norm indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L88-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.sq_norm_indicator (Qz : Set ℂ) (f : ℂ → H) :
    (fun z => ‖Qz.indicator f z‖ ^ 2) = Qz.indicator (fun z => ‖f z‖ ^ 2) := by sorry
