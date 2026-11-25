-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_rhoR_pow
-- name    : Formalism.FourierDecayAlt.P.PBK.norm_rhoR_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:22:17.256176+00:00
-- url     : https://prove2.me/theorems/54b9174e-b0df-4ac0-999d-fdd8750c35f9
-- title:
--   PBK: norm rho R pow
-- statement:
--   The PBK construction uses the norm rho R pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean#L85-L87

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.PBK.norm_rhoR_pow {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    ‖rhoR s σ x‖ ^ s = ‖x ^ (s - 1) / (x + σ) ^ (s - 1)‖ := by sorry
