-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integrable_inner_of_memLp
-- name    : Formalism.FourierDecayAlt.P.PBK.integrable_inner_of_memLp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:01:15.429903+00:00
-- url     : https://prove2.me/theorems/6356cd7f-3ce3-4b58-9059-cc5755ab7669
-- title:
--   PBK: integrable inner of mem Lp
-- statement:
--   The PBK construction uses the integrable inner of mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean#L26-L30

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.PBK.integrable_inner_of_memLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun D => ⟪f D, g D⟫_ℂ) μ := by sorry
