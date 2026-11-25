-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_psi_conv
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi_conv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:21.719599+00:00
-- url     : https://prove2.me/theorems/2166fb50-409e-4ba5-9566-16b41c8a8d85
-- title:
--   PBK: tendsto integral psi conv
-- statement:
--   The PBK construction uses the tendsto integral psi conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralPsiMoving.lean#L91-L106

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

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi_conv {α : Type} {l : Filter α} (β : ℂ) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (σ : ℂ) (hw : Tendsto w l (𝓝 σ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 (∫ z, G.psi β (σ * z) • f0 z)) := by sorry
