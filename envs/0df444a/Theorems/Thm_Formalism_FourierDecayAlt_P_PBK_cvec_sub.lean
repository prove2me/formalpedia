-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_cvec_sub
-- name    : Formalism.FourierDecayAlt.P.PBK.cvec_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:40:03.777219+00:00
-- url     : https://prove2.me/theorems/8bae3380-3f0c-45d3-b186-4bfe6257c7a5
-- title:
--   PBK: cvec sub
-- statement:
--   The PBK construction uses the cvec sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralNormCvecSq.lean#L76-L78

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

theorem Formalism.FourierDecayAlt.P.PBK.cvec_sub (s : ℕ) (F G : ℂ → ℂ → H) (x c : ℂ) :
    cvec s F x c - cvec s G x c = cvec s (fun x D => F x D - G x D) x c := by sorry
