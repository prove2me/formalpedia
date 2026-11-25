-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_cvec_eq_comp
-- name    : Formalism.FourierDecayAlt.P.PBK.cvec_eq_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:21:22.580554+00:00
-- url     : https://prove2.me/theorems/8411a2aa-9f55-4476-939f-566fbf13abee
-- title:
--   PBK: cvec eq comp
-- statement:
--   The PBK construction uses the cvec eq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean#L58-L61

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

theorem Formalism.FourierDecayAlt.P.PBK.cvec_eq_comp (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) :
    cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by sorry
