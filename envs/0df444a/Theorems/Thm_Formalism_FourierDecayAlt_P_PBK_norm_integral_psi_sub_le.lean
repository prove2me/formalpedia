-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_integral_psi_sub_le
-- name    : Formalism.FourierDecayAlt.P.PBK.norm_integral_psi_sub_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:52:49.455643+00:00
-- url     : https://prove2.me/theorems/34a7edfa-6cba-47eb-a162-89696f7094fb
-- title:
--   PBK: norm integral psi sub le
-- statement:
--   The PBK construction uses the norm integral psi sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean#L53-L64

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

theorem Formalism.FourierDecayAlt.P.PBK.norm_integral_psi_sub_le (β w : ℂ) (f g : ℂ → E) (hf : Integrable f) (hg : Integrable g) :
    ‖(∫ z, G.psi β (w * z) • f z) - ∫ z, G.psi β (w * z) • g z‖ ≤ ∫ z, ‖f z - g z‖ := by sorry
