-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_psi
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:52:13.81452+00:00
-- url     : https://prove2.me/theorems/1b9e3b21-9b45-4608-974b-0702e2f99c91
-- title:
--   PBK: tendsto integral psi
-- statement:
--   The PBK construction uses the tendsto integral psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean#L45-L51

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi (β : ℂ) (hβ : β ≠ 0) (f : ℂ → E) :
    Tendsto (fun w => ∫ z, G.psi β (w * z) • f z) (cocompact ℂ) (𝓝 0) := by sorry
