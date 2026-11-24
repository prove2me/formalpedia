-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_comp
-- name    : Formalism.FourierDecayAlt.P.PBA.blockPSD_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:31:29.108465+00:00
-- url     : https://prove2.me/theorems/2f1df987-f8e5-4332-946c-ee571a36346f
-- title:
--   PBA: block PSD comp
-- statement:
--   The PBA construction uses the block PSD comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L38-L50

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section

theorem Formalism.FourierDecayAlt.P.PBA.blockPSD_comp {α X : Type} (Y₀ : Finset α) (a w b : α → α → ℂ) (h : KB.BlockPSD Y₀ Y₀ a w b)
    (Y : Finset X) (l : X → α) (hl : ∀ x ∈ Y, l x ∈ Y₀) :
    KB.BlockPSD Y Y (fun x y => a (l x) (l y)) (fun x y => w (l x) (l y)) (fun x y => b (l x) (l y)) := by sorry
