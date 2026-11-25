-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_sq_le_eta
-- name    : Formalism.FourierDecayAlt.P.PBK.norm_sq_le_eta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:53.331906+00:00
-- url     : https://prove2.me/theorems/04a42beb-7e24-406d-9b10-8442e66dcebe
-- title:
--   PBK: norm sq le eta
-- statement:
--   The PBK construction uses the norm sq le eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L70-L80

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

theorem Formalism.FourierDecayAlt.P.PBK.norm_sq_le_eta (a u : H) (η : ℝ) (hη : 0 < η) :
    ‖a‖ ^ 2 ≤ (1 + η) * ‖u‖ ^ 2 + (1 + η⁻¹) * ‖u - a‖ ^ 2 := by sorry
