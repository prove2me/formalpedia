-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_blockPSD_gram
-- name    : Formalism.FourierDecayAlt.P.PBK.blockPSD_gram
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:28.57226+00:00
-- url     : https://prove2.me/theorems/fb595ae2-ac77-4299-8cf9-10db0dc0017c
-- title:
--   PBK: block PSD gram
-- statement:
--   The PBK construction uses the block PSD gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockPSDCongr.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockPSDCongr.lean#L27-L34

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
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

theorem Formalism.FourierDecayAlt.P.PBK.blockPSD_gram {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) (f : α → H) (g : β → H) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ⟪f p, f q⟫_ℂ) (fun p q => ⟪f p, g q⟫_ℂ) (fun p q => ⟪g p, g q⟫_ℂ) := by sorry
