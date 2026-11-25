-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_smul_cocompact
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_smul_cocompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:35.13352+00:00
-- url     : https://prove2.me/theorems/0ec27bb4-0435-54a9-a825-bcfa807c72b4
-- title:
--   PBK: tendsto smul cocompact
-- statement:
--   The PBK construction uses the tendsto smul cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean#L101-L105

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
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

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_smul_cocompact {α : Type} {l : Filter α} (c : ℂ) (hc : c ≠ 0) (y : α → ℂ)
    (hy : Tendsto y l (cocompact ℂ)) : Tendsto (fun a => c * y a) l (cocompact ℂ) := by sorry
